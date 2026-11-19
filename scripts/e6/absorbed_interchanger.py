"""Check the crossing diagrams in Researcher Response 1 of r4."""

from dataclasses import dataclass


@dataclass(frozen=True)
class Edge:
    """A contextual ι. Its source executes right then left."""

    pre: tuple
    left: str
    right: str
    post: tuple

    def source(self):
        return self.pre + (self.right, self.left) + self.post

    def target(self):
        return self.pre + (self.left, self.right) + self.post

    def before(self, path):
        return Edge(path + self.pre, self.left, self.right, self.post)

    def after(self, path):
        return Edge(self.pre, self.left, self.right, self.post + path)


def run(word, path):
    word = list(word)
    for i, j in path:
        pos = word.index("b" + j)
        assert word[pos + 1] == "a" + i
        word[pos : pos + 2] = reversed(word[pos : pos + 2])
    return tuple(word)


def check_edge(word, edge):
    middle = run(word, edge.pre)
    left_pos = middle.index("b" + edge.left[1])
    right_pos = middle.index("b" + edge.right[1])
    assert left_pos + 1 < right_pos
    assert run(word, edge.source()) == run(word, edge.target())


def project(edge, a, b):
    def keep(path):
        return tuple(c for c in path if c[0] != a and c[1] != b)

    assert keep((edge.left, edge.right)) == (edge.left, edge.right)
    return Edge(keep(edge.pre), edge.left, edge.right, keep(edge.post))


def check_square(word, x, y, absorbed, probe, context):
    # Right first, then left. Left first, then right.
    routes = ((y.before(x.source()), x.after(y.target())),
              (x.after(y.source()), y.before(x.target())))
    for first, second in routes:
        check_edge(word, first)
        check_edge(word, second)
        assert first.target() == second.source()
    assert routes[0][0].source() == routes[1][0].source()
    assert routes[0][1].target() == routes[1][1].target()
    reduced = []
    for route in routes:
        killed, = [edge for edge in route if absorbed(edge)]
        live, = [edge for edge in route if (edge.left, edge.right) == probe]
        assert killed != live
        # The context equality is supplied by the boundary of the identity
        # that absorbed the other edge. Check the actual site of replacement.
        side, old, new = context
        path = getattr(live, side)
        assert path in (old, new)
        reduced.append((live.left, live.right,
                        new if side == "pre" else live.pre,
                        new if side == "post" else live.post))
    assert reduced[0] == reduced[1]


def check_thin_block():
    # Two consecutive variations in V of (K38). Every corner is a full
    # crossing of the 3-by-2 rectangle.
    start = ("b1", "b2", "a1", "a2", "a3")
    end = ("a1", "a2", "a3", "b1", "b2")
    x = Edge(("12",), "11", "22", ())
    y = Edge((), "21", "32", ("31",))
    for edge in (y.before(x.source()), x.after(y.target()),
                 x.after(y.source()), y.before(x.target())):
        check_edge(start, edge)
        assert run(start, edge.source()) == run(start, edge.target()) == end

    # Enumerate the two shorter 3-path intervals in the 2-by-2 projections.
    small_start = ("b1", "b2", "a1", "a2")
    small_end = ("a1", "a2", "b1", "b2")
    e = Edge((), "11", "22", ())
    for initial, final, short in (
        (small_start, run(small_start, x.source()), x),
        (run(small_start, ("12",)), small_end, e.after(("21",))),
    ):
        stack = [(initial, ())]
        paths = set()
        while stack:
            word, path = stack.pop()
            if word == final:
                paths.add(path)
                continue
            for b, a in zip(word, word[1:]):
                if b[0] == "b" and a[0] == "a":
                    crossing = a[1] + b[1]
                    stack.append((run(word, (crossing,)), path + (crossing,)))
        assert paths == {short.source(), short.target()}
        check_edge(initial, short)


def main():
    e = Edge((), "11", "22", ())
    p, q = ("12",), ("21",)
    u, v = e.source(), e.target()

    # X = p e, Y = q J. Contracting a2 and b1 projects Y to bare J.
    j = Edge((), "10", "32", ())
    x, y = e.before(p), j.before(q)
    assert project(x, "3", "0") == e.before(p)
    assert project(y, "2", "1") == j
    check_square(
        ("b0", "b1", "b2", "a1", "a2", "a3"), x, y,
        lambda z: (z.left, z.right) == (e.left, e.right)
        and z.pre == p and z.post[:1] == q,
        (j.left, j.right), ("pre", p + u + q, p + v + q))

    # X = J p, Y = e. Contracting a1 and b2 projects X to bare J.
    j = Edge((), "01", "23", ())
    x, y = j.after(p), e
    assert project(x, "1", "2") == j
    assert project(y, "0", "3") == e
    check_square(
        ("b1", "a0", "b2", "a1", "b3", "a2"), x, y,
        lambda z: (z.left, z.right) == (e.left, e.right)
        and z.pre[-1:] == p and not z.post,
        (j.left, j.right), ("post", p + u, p + v))
    print("Both 3-by-3 squares type-check. In each case the two routes "
          "reduce to the same contextual probe.")
    check_thin_block()
    print("All four 3-by-2 corners are extreme. Each projected input "
          "interval has exactly two paths.")


if __name__ == "__main__":
    main()
