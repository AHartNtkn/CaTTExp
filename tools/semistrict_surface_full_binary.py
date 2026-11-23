"""Normalize well-typed ordinary terms on the A,U,I binary surface.

Use evaluate(term, generators(ctx)) for the catt.py constructor signature.
word_representative(P, cell) returns a raw word tree, or None, on a globular P.
"""
from dataclasses import dataclass
from functools import cache

from catt import STAR, glue_tree, is_ps, maximal_vars, side_ok, subst_ty, tdim, tree_ctx, ucomp


@dataclass(frozen=True)
class Cell:
    rank: int
    source: object
    target: object
    events: tuple


@dataclass(frozen=True)
class Atom:
    name: tuple
    source: Cell
    target: Cell


@dataclass(frozen=True)
class Whisker:
    cut: int
    right: bool
    inner: object
    stationary: Cell


def variable(index, ty):
    if ty is None:
        return Cell(0, None, None, (index,))
    s, t = ty
    return Cell(s.rank + 1, s, t, (Atom(('v', index), s, t),))


def unit(a):
    return Cell(a.rank + 1, a, a, ())


@cache
def end(event, positive):
    if isinstance(event, Atom):
        return event.target if positive else event.source
    moving = end(event.inner, positive)
    if event.right:
        return compose(event.cut, event.stationary, moving)
    return compose(event.cut, moving, event.stationary)


def swap(a, b):
    """The directed adjacent exchange, including its common exterior contexts."""
    if not isinstance(a, Whisker) or not isinstance(b, Whisker) or a.cut != b.cut:
        return None
    if a.right == b.right:
        if a.stationary != b.stationary:
            return None
        inner = swap(a.inner, b.inner)
        if inner is None:
            return None
        return tuple(Whisker(a.cut, a.right, e, a.stationary) for e in inner)
    if not a.right or a.stationary != end(b.inner, False) or b.stationary != end(a.inner, True):
        return None
    return (Whisker(a.cut, False, b.inner, end(a.inner, False)),
            Whisker(a.cut, True, a.inner, end(b.inner, True)))


@cache
def sorted_events(events):
    events = list(events)
    i = 0
    while i + 1 < len(events):
        change = swap(events[i], events[i + 1])
        if change is None:
            i += 1
        else:
            events[i:i + 2] = change
            i = max(0, i - 1)
    return tuple(events)


@cache
def compose(cut, a, b):
    if not 0 <= cut < min(a.rank, b.rank):
        raise ValueError('cut is outside an operand')
    n = max(a.rank, b.rank)
    if cut == n - 1:
        if a.target != b.source:
            raise ValueError('different top seam')
        return Cell(n, a.source, b.target, sorted_events(a.events + b.events))
    a0, a1 = (a.source, a.target) if a.rank == n else (a, a)
    b0, b1 = (b.source, b.target) if b.rank == n else (b, b)
    source = compose(cut, a0, b0)
    target = compose(cut, a1, b1)
    left = tuple(Whisker(cut, False, e, b0) for e in a.events) if a.rank == n else ()
    right = tuple(Whisker(cut, True, e, a1) for e in b.events) if b.rank == n else ()
    return Cell(n, source, target, sorted_events(left + right))


@cache
def generators(ctx):
    if not ctx:
        return ()
    env = generators(ctx[:-1])
    ty = ctx[-1]
    faces = None if ty == STAR else tuple(evaluate(face, env) for face in ty[2:])
    return env + (variable(len(env), faces),)


@cache
def binary_shape(arity):
    maxima = maximal_vars(arity)
    if len(maxima) != 2:
        return None
    a, b = maxima
    p, q = (tdim(arity[i]) + 1 for i in maxima)
    for cut in range(min(p, q)):
        if tree_ctx(glue_tree(p, cut, q)) == arity:
            return cut, a, b
    return None


@cache
def evaluate(term, env):
    if term[0] == 'v':
        return env[term[1]]
    _, arity, ty, sub = term
    generic = generators(arity)
    s, t = (evaluate(face, generic) for face in ty[2:])
    labels = tuple(evaluate(arg, env) for arg in sub)
    binary = binary_shape(arity)
    if binary is not None:
        cut, a, b = binary
        biased = ucomp(arity)[2]
        if (tdim(ty) == tdim(biased)
                and (s, t) == tuple(evaluate(face, generic) for face in biased[2:])):
            return compose(cut, labels[a], labels[b])
    actual_s = evaluate(ty[2], labels)
    if s == t and word_representative(arity, s) is not None:
        return unit(actual_s)
    actual_t = evaluate(ty[3], labels)
    name = ('head', arity, s, t, labels)
    return Cell(s.rank + 1, actual_s, actual_t, (Atom(name, actual_s, actual_t),))


class NoWord(Exception):
    pass


class WordProblem:
    """Solve literal word and face equations with prescribed history values on a globular set."""
    def __init__(self, arity):
        self.arity = arity
        self.env = generators(arity)
        self.values = {}
        self.solutions = {}
        self.faces = {}
        self.equations = []

    def unknown(self, value):
        x = ('?', len(self.values))
        self.values[x] = value
        return x

    def resolve(self, expr):
        if expr in self.solutions:
            return self.resolve(self.solutions[expr])
        if expr[0] == 'id':
            return 'id', self.resolve(expr[1])
        if expr[0] == 'bin':
            return 'bin', expr[1], self.resolve(expr[2]), self.resolve(expr[3])
        return expr

    def value(self, expr):
        tag = expr[0]
        if tag == '?':
            return self.values[expr]
        if tag == 'v':
            return self.env[expr[1]]
        if tag == 'id':
            return unit(self.value(expr[1]))
        return compose(expr[1], self.value(expr[2]), self.value(expr[3]))

    def face(self, expr, positive):
        tag = expr[0]
        if tag == '?':
            key = expr, positive
            if key not in self.faces:
                value = self.values[expr]
                self.faces[key] = self.unknown(value.target if positive else value.source)
            return self.faces[key]
        if tag == 'v':
            return self.arity[expr[1]][3 if positive else 2]
        if tag == 'id':
            return expr[1]
        _, cut, left, right = expr
        a, b = self.value(left), self.value(right)
        n = max(a.rank, b.rank)
        if cut == n - 1:
            return self.face(right if positive else left, positive)
        return ('bin', cut, self.face(left, positive) if a.rank == n else left,
                self.face(right, positive) if b.rank == n else right)

    def incidence(self, expr):
        if expr[0] == 'id':
            self.incidence(expr[1])
        if expr[0] != 'bin':
            return
        _, cut, left, right = expr
        for side in (left, right):
            self.incidence(side)
        for _ in range(self.value(left).rank - cut):
            left = self.face(left, True)
        for _ in range(self.value(right).rank - cut):
            right = self.face(right, False)
        self.equations.append((left, right))

    def template(self, value):
        if value.rank == 0:
            return 'v', value.events[0]
        if not value.events:
            return 'id', self.unknown(value.source)
        locations = []
        leaves = {}
        nodes = {}
        for e in value.events:
            address = ()
            while isinstance(e, Whisker):
                cut, labels = nodes.setdefault(address, (e.cut, {}))
                if cut != e.cut:
                    raise NoWord
                labels.setdefault(not e.right, e.stationary)
                address += (e.right,)
                e = e.inner
            if e.name[0] != 'v':
                raise NoWord
            leaves.setdefault(address, self.face(e.name, False))
            locations.append((address, e.name))
        if leaves.keys() & nodes.keys():
            raise NoWord
        for addr, (_, labels) in nodes.items():
            for right in (False, True):
                child = addr + (right,)
                if child not in leaves and child not in nodes:
                    leaves[child] = self.unknown(labels[right])

        def tree(addr=()):
            if addr in leaves:
                return leaves[addr]
            return 'bin', nodes[addr][0], tree(addr + (False,)), tree(addr + (True,))

        result = None
        for addr, atom in locations:
            if leaves[addr] != self.face(atom, False):
                raise NoWord
            leaves[addr] = atom
            step = tree()
            leaves[addr] = self.face(atom, True)
            result = step if result is None else ('bin', value.rank - 1, result, step)
        if self.value(result) != value:
            raise NoWord
        return result

    def unify(self, left, right, rank):
        left, right = self.resolve(left), self.resolve(right)
        if left == right:
            return
        if self.value(left) != self.value(right):
            raise NoWord
        if self.value(left).rank < rank:
            self.equations.append((left, right))
            return
        if left[0] == '?' or right[0] == '?':
            if left[0] != '?':
                left, right = right, left

            def occurs(expr):
                if expr[0] == 'bin':
                    return occurs(expr[2]) or occurs(expr[3])
                if expr[0] == 'id':
                    return occurs(expr[1])
                return expr == left

            if occurs(right):
                raise NoWord
            self.solutions[left] = right
        elif left[0] == right[0] == 'id':
            self.unify(left[1], right[1], rank)
        elif left[:2] == right[:2] and left[0] == 'bin':
            self.unify(left[2], right[2], rank)
            self.unify(left[3], right[3], rank)
        else:
            raise NoWord

    def solve(self, root):
        for rank in range(self.values[root].rank, -1, -1):
            pending, self.equations = self.equations, []
            for left, right in pending:
                self.unify(left, right, rank)
            xs = [x for x, val in self.values.items() if val.rank == rank]
            for x in xs:
                if x not in self.solutions:
                    self.solutions[x] = self.template(self.values[x])
            for x in xs:
                chosen = self.resolve(x)
                self.incidence(chosen)
                for positive in (False, True):
                    if (x, positive) in self.faces:
                        self.equations.append((self.faces[x, positive], self.face(chosen, positive)))
        if any(self.resolve(a) != self.resolve(b) for a, b in self.equations):
            raise NoWord
        return self.resolve(root)


@cache
def word_representative(arity, value):
    try:
        problem = WordProblem(arity)
        return problem.solve(problem.unknown(value))
    except (NoWord, ValueError):
        return None

@cache
def type_value(ctx, ty):
    if ty == STAR:
        return STAR
    env = generators(ctx)
    return type_value(ctx, ty[1]), evaluate(ty[2], env), evaluate(ty[3], env)


@cache
def check_surface_type(ctx, ty):
    if ty == STAR:
        return
    check_surface_type(ctx, ty[1])
    expected = type_value(ctx, ty[1])
    for face in ty[2:]:
        if type_value(ctx, infer_surface(ctx, face)) != expected:
            raise ValueError('face fails surface type conversion')


@cache
def infer_surface(ctx, term):
    """Check an ordinary constructor expression with conversion in a well-formed context."""
    if term[0] == 'v':
        if not 0 <= term[1] < len(ctx):
            raise ValueError('variable is outside the context')
        return ctx[term[1]]
    _, arity, ty, labels = term
    if ty == STAR or not is_ps(arity) or len(labels) != len(arity):
        raise ValueError('invalid coherence arity or labelling')
    check_surface_type(arity, ty)
    if not side_ok(arity, ty[1], ty[2], ty[3]):
        raise ValueError('coherence fails the ordinary arity condition')
    for declared, label in zip(arity, labels):
        expected = subst_ty(declared, labels)
        if type_value(ctx, infer_surface(ctx, label)) != type_value(ctx, expected):
            raise ValueError('label fails surface type conversion')
    return subst_ty(ty, labels)
