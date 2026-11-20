#!/usr/bin/env python3
"""Check persistent exterior words on actual two-faces of raw three-generators."""
from fibration_factor_search import Stage, Rule
from fibration_ordinal_pentagon import simplex


def idle(stage, pole, word, path):
    """Nonempty prefix/suffix words which remain an identity whisker throughout."""
    faces = tuple(stage.slices(pole, word, path))
    left, right = set(), set()
    for n in range(1, len(word) + 1):
        if all(i >= n for _, i in path):
            left.add(word[:n])
        if all(i + len(stage.rules[name].source) <= len(w) - n
               for w, (name, i) in zip(faces, path)):
            right.add(word[-n:])
    return left, right


def check():
    checked = 0
    for gap in (0, 1):
        stage, _, _, disks, *_ = simplex(gap)
        for pole, word, src, tgt in disks.values():
            for path in (src, tgt):
                assert idle(stage,pole,word,path) == (set(),set())
                checked += 1

    # Source fibre fg=>k, with f erased and g sent to xy. Transport of the
    # 2-generator is the two-step path xy=>uv=>z at the terminal vertex.
    arrows = {c: ("X","X") for c in "fgk"}
    arrows.update({c: ("Y","Y") for c in "xyuvz"})
    arrows["t"] = ("X","Y")
    rules = {"r": Rule("X","fg","k"), "e": Rule("Y","xy","uv"),
             "d": Rule("Y","uv","z"), "f": Rule("X","t","tf"),
             "g": Rule("X","xyt","tg"), "k": Rule("X","zt","tk")}
    stage = Stage(arrows,rules)
    src = (("g",0),("f",0),("r",1))
    tgt = (("e",0),("d",0),("k",0))
    for path in (src,tgt):
        assert tuple(stage.slices("X","xyt",path))[-1] == "tk"
        assert idle(stage,"X","xyt",path) == (set(),set())
        checked += 1

    # A base 3-face with a real idle wire. Its object lift has precisely the
    # same idle base edge even when its triangle component is nonidentity.
    stage = Stage({c: ("x","x") for c in "abg"},
                  {"u": Rule("x","gbb","b"), "v": Rule("x","gbb","b")})
    for k in ("u","v"):
        assert idle(stage,"x","gbba",((k,0),)) == (set(),{"a"})
    # Dropping positivity of the fibre 2-source really adds a mixed idle word.
    stage = Stage({"t": ("X","Y"), "k": ("X","X")},
                  {"r": Rule("X","","k"), "c": Rule("X","t","tk")})
    assert idle(stage,"X","t",(("r",1),)) == ({"t"},set())
    assert idle(stage,"X","t",(("c",0),)) == (set(),set())
    print(f"{checked} tested faces of mixed or tetrahedral disks have no idle exterior word")
    print("Whiskered object faces retain the base suffix; the nullary control has a mixed idle prefix")


if __name__ == "__main__":
    check()
