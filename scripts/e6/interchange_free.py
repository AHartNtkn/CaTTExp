"""Compile the graded fragment of P on a globular pasting tree to a finite graph."""
from collections import defaultdict, deque
from dataclasses import dataclass
from itertools import product

from interchange_reachability import Edge, Path, Presentation, Rule, query_cli
from reachability_theory import EQUATIONS, OPERATIONS, RULES


@dataclass(frozen=True)
class CellData:
    dimension: int
    source: int
    target: int
    size: int
    moment: int = 0


def tree_generators(tree):
    """A list is the wedge of the suspensions of its children. [] is one vertex."""
    generators, globes = {}, []

    def visit(node, path, faces):
        if not isinstance(node, list):
            raise ValueError('a pasting tree must be a nested JSON array')
        names = ['/'.join(map(str, (*path, i))) for i in range(len(node) + 1)]
        if len(path) <= 4:
            for name in names:
                generators[name] = (len(path), faces)
        else:
            for name in names:
                globes.append((name, *faces))
        for i, child in enumerate(node):
            if len(path) < 5:
                visit(child, (*path, i), (names[i], names[i+1]))
            else:
                validate_tree(child)

    def validate_tree(node):
        if not isinstance(node, list):
            raise ValueError('a pasting tree must be a nested JSON array')
        for child in node:
            validate_tree(child)

    visit(tree, (), None)
    return generators, globes


def dimension(expr, variables):
    if isinstance(expr, str):
        return variables[expr]
    return OPERATIONS[expr[0]].output


def selector(name):
    return len(name) == 2 and name[0] in 'st' and name[1].isdigit()


class FreeAlgebra:
    """Ground operation tables, modulo congruence, one dimension at a time."""
    def __init__(self, tree):
        generators, self.globes = tree_generators(tree)
        self.generators = {}
        self.data = []
        self.parent = []
        self.table = {}
        self.coefficient = None
        self.cap = None
        for name, (dim, faces) in generators.items():
            s, t = (self.generators[f] for f in faces) if faces else (-1, -1)
            self.generators[name] = self.new(CellData(dim, s, t, 1))
        for dim in range(1, 4):
            self.complete(dim)
        self.lower_table_size = len(self.data)
        self.coefficient = (1 + max(self.data[x].size for x in self.domain(2))
                            + max(self.data[x].size for x in self.domain(3)))

    def new(self, data):
        x = len(self.data)
        self.data.append(data)
        self.parent.append(x)
        return x

    def root(self, x):
        while x != self.parent[x]:
            self.parent[x] = self.parent[self.parent[x]]
            x = self.parent[x]
        return x

    def domain(self, dim):
        return [i for i, data in enumerate(self.data) if data.dimension == dim
                and self.parent[i] == i and (dim != 4 or self.cap is None or data.size <= self.cap)]

    def merge(self, x, y):
        x, y = self.root(x), self.root(y)
        if x == y:
            return False
        if self.data[x] != self.data[y]:
            raise ValueError(f'equation changes boundary or grading: {self.data[x]}, {self.data[y]}')
        self.parent[max(x, y)] = min(x, y)
        return True

    def rebuild(self):
        while True:
            compact = {}
            changed = False
            for (name, args), x in self.table.items():
                key = (name, tuple(map(self.root, args)))
                if key in compact:
                    changed |= self.merge(compact[key], x)
                compact[key] = self.root(x)
            self.table = compact
            if not changed:
                return

    def value(self, expr, env):
        if isinstance(expr, str):
            return self.root(env[expr])
        name = expr[0]
        args = tuple(self.value(child, env) for child in expr[1:])
        if None in args:
            return None
        if selector(name):
            data = self.data[args[0]]
            return data.source if name[0] == 's' else data.target
        result = self.table.get((name, args))
        return None if result is None else self.root(result)

    def compatible(self, guards, env):
        for lhs, rhs in guards:
            l, r = self.value(lhs, env), self.value(rhs, env)
            if l is None or r is None or l != r:
                return False
        return True

    def metrics(self, name, args):
        if name.startswith('id'):
            return 0, 0
        a, b = args
        if name.startswith('comp'):
            return a.size + b.size, a.moment + b.moment
        if name.startswith(('left', 'right')):
            left = name.startswith('left')
            low, high = (a, b) if left else (b, a)
            offset = 0
            if high.dimension == 3 and low.dimension == 2:
                offset = (-1 if left else 1) * low.size * high.size
            return high.size, high.moment + offset
        if name == 'chi' or name == 'iota':
            return a.size * b.size, 0
        if name == 'r':
            return b.size * (self.coefficient * a.size + a.moment), 0
        if name == 't':
            return a.size * (self.coefficient * b.size - b.moment), 0
        if name == 'h':
            width = self.data[b.target].size
            return width * (self.coefficient * a.size + a.moment) - a.size * b.size, 0
        raise ValueError(f'unknown graded operation {name}')

    def describe(self, name, args):
        op = OPERATIONS[name]
        env = {f'x{i}': x for i, x in enumerate(args)}
        if not self.compatible(op.guards, env):
            return None
        s, t = self.value(op.source, env), self.value(op.target, env)
        if s is None or t is None:
            raise RuntimeError(f'incomplete lower-dimensional table for {name}')
        size, moment = self.metrics(name, tuple(self.data[x] for x in args))
        if size < 0:
            raise ValueError(f'negative weight in {name}')
        return CellData(op.output, s, t, size, moment)

    def insert(self, name, args):
        key = name, args
        if key in self.table:
            return
        data = self.describe(name, args)
        if data is None or data.dimension == 4 and data.size > self.cap:
            return
        # Category units and trivial actions are frequent. These shortcuts are
        # consequences of the declared laws; no nonidentity arrows are identified.
        result = None
        if not name.startswith('id') and data.size == 0:
            if data.source != data.target:
                raise ValueError(f'zero-size {name} with unequal endpoints')
            result = self.table.get((f'id{data.dimension-1}', (data.source,)))
        elif name.startswith(('comp', 'left', 'right')) and len(args) == 2:
            a, b = (self.data[x] for x in args)
            if a.size == 0 and b.dimension == data.dimension:
                result = args[1]
            elif b.size == 0 and a.dimension == data.dimension:
                result = args[0]
        if result is not None and self.data[self.root(result)] != data:
            raise ValueError(f'incorrect normalized boundary in {name}')
        self.table[key] = self.new(data) if result is None else self.root(result)

    def assignments(self, schema, domains):
        # Test each guard as soon as its last variable is bound. This matters
        # for equations on several consecutive, often noncomposable, cells.
        def names(expr):
            return {expr} if isinstance(expr, str) else set().union(*(names(x) for x in expr[1:]))
        variables = schema.variables
        position = {v: i for i, (v, _) in enumerate(variables)}
        by_last = defaultdict(list)
        for a, b in schema.guards:
            last = max(position[v] for v in names(a) | names(b))
            by_last[last].append((a, b))
        env = {}
        def extend(i):
            if i == len(variables):
                yield env
                return
            var, dim = variables[i]
            for x in domains[dim]:
                env[var] = x
                if self.compatible(by_last[i], env):
                    yield from extend(i+1)
        yield from extend(0)

    def complete(self, dim):
        ops = [(name, op) for name, op in OPERATIONS.items()
               if op.output == dim and not selector(name)]
        equations = [eq for eq in EQUATIONS
                     if max(d for _, d in eq.variables) <= dim
                     and dimension(eq.left, dict(eq.variables)) == dim]
        while True:
            before = len(self.table)
            domains = [self.domain(i) for i in range(dim+1)]
            for name, op in ops:
                for args in product(*(domains[d] for d in op.inputs)):
                    self.insert(name, args)
            # Stage the equalities, then rebuild. During grounding, every lookup
            # sees the same representatives (including guards at this degree).
            merges = []
            for eq in equations:
                for env in self.assignments(eq, domains):
                    x, y = self.value(eq.left, env), self.value(eq.right, env)
                    if x is not None and y is not None and x != y:
                        merges.append((x,y))
            for x, y in merges:
                self.merge(x, y)
            if merges:
                self.rebuild()
            elif before == len(self.table):
                return

    def query_term(self, expr):
        # Before a cap is known, evaluate only the shape, weight and boundaries
        # of each 4-subterm. Taking a face of a large term still works.
        if isinstance(expr, str):
            if expr not in self.generators:
                raise ValueError(f'unknown generator {expr!r} in dimensions zero through four')
            return self.root(self.generators[expr])
        if not isinstance(expr, (list, tuple)) or not expr or not isinstance(expr[0], str):
            raise ValueError('a term must be a generator name or an operation application')
        name, *children = expr
        if name not in OPERATIONS:
            raise ValueError(f'unknown operation {name!r}')
        op = OPERATIONS[name]
        args = tuple(self.query_term(child) for child in children)
        if tuple(self.data[x].dimension for x in args) != op.inputs:
            raise ValueError(f'wrong argument dimensions in {name}')
        if selector(name):
            data = self.data[args[0]]
            return data.source if name[0] == 's' else data.target
        if op.output < 4:
            result = self.table.get((name,args))
            if result is None:
                raise ValueError(f'ill-typed application of {name}')
            return self.root(result)
        data = self.describe(name, args)
        if data is None:
            raise ValueError(f'ill-typed application of {name}')
        if self.cap is None or data.size > self.cap:
            # Temporary descriptors are discarded before completing degree four.
            return self.new(data)
        return self.root(self.table[name,args])

    def query(self, source, target):
        # Keep the finite lower skeleton when the same tree receives a new query.
        # Class identifiers in certificates must depend only on the current query.
        if self.cap is not None:
            self.cap = None
            self.table = {key: val for key, val in self.table.items()
                          if OPERATIONS[key[0]].output < 4}
        mark = self.lower_table_size
        del self.data[mark:]
        del self.parent[mark:]
        try:
            a, b = self.query_term(source), self.query_term(target)
            p, q = self.data[a], self.data[b]
        finally:
            del self.data[mark:]
            del self.parent[mark:]
        if p.dimension != 4 or q.dimension != 4 or (p.source,p.target) != (q.source,q.target):
            raise ValueError('the query requires parallel 4-terms')
        self.cap = max(p.size, q.size)
        self.complete(4)
        a, b = self.query_term(source), self.query_term(target)
        cells = self.domain(4)
        domains = [self.domain(i) for i in range(5)]
        base = {}
        def record(x,y,label):
            if x != y and (x,y) not in base:
                if self.data[x].size < self.data[y].size:
                    raise ValueError(f'grading increases at {label}')
                base[x,y] = label
        for name, s, t in self.globes:
            x, y = self.generators[s], self.generators[t]
            if self.data[x].size <= self.cap:
                record(self.root(x),self.root(y),'globe '+name)
        for rule in RULES:
            for env in self.assignments(rule, domains):
                x, y = self.value(rule.left,env), self.value(rule.right,env)
                if x is not None and y is not None:
                    record(x,y,rule.name+' '+','.join(str(env[v]) for v,_ in rule.variables))
        contexts = defaultdict(dict)
        for (name,args), val in self.table.items():
            op = OPERATIONS[name]
            if op.output == 4:
                for i,d in enumerate(op.inputs):
                    if d == 4:
                        fixed = (name,i,args[:i]+args[i+1:])
                        contexts[args[i]][fixed] = self.root(val)
        queue = deque(base)
        while queue:
            x,y = queue.popleft()
            for fixed in sorted(contexts[x].keys() & contexts[y].keys()):
                u,v = contexts[x][fixed],contexts[y][fixed]
                if u != v and (u,v) not in base:
                    record(u,v,f'{fixed} of ({x},{y})')
                    queue.append((u,v))
        def path(x):
            d = self.data[x]
            return Path(str(d.source), (str(x),) if d.size else ())
        edges = {str(x): Edge(str(self.data[x].source),str(self.data[x].target),self.data[x].size)
                 for x in cells if self.data[x].size}
        rules = [Rule(f'{x}>{y} {label}',path(x),path(y)) for (x,y),label in sorted(base.items())]
        return Presentation(map(str, domains[3]),edges,rules),path(a),path(b)


def compile_query(tree, source, target):
    return FreeAlgebra(tree).query(source,target)


def read_query(data):
    return compile_query(data['tree'], data['source'], data['target'])


if __name__ == '__main__':
    query_cli(read_query, __doc__)
