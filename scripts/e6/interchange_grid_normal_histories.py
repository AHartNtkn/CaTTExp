"""Check the proposed normal histories against the round-5 contextual K15 graph."""
from itertools import combinations_with_replacement

from grid_loop_words import classes


def normal(start, schedule):
    height = list(start)
    result = []
    segment = []
    on_diagonal = height[0] == height[1]
    for row, b in schedule:
        assert b == height[row]
        height[row] -= 1
        segment.append((row, b))
        if height[0] == height[1]:
            half = len(segment) // 2
            if (on_diagonal and all(i == 0 for i, _ in segment[:half])
                    and all(i == 1 for i, _ in segment[half:])):
                for first, second in zip(segment[:half], segment[half:]):
                    result.extend((first, second))
            else:
                result.extend(segment)
            segment = []
            on_diagonal = True
    return tuple(result + segment)


def run(n):
    states = list(combinations_with_replacement(range(n + 1), 2))
    intervals = histories = total_classes = 0
    for s in states:
        for t in states:
            if any(x < y for x, y in zip(s, t)):
                continue
            intervals += 1
            table = classes(s, t)
            representatives = {}
            for h, oracle in table.items():
                word = normal(s, h)
                assert table[word] == oracle
                assert representatives.setdefault(oracle, word) == word
            histories += len(table)
            total_classes += len(representatives)
    print(f'{len(states)} states, {intervals} intervals, {histories} histories, {total_classes} normal forms')


if __name__ == '__main__':
    run(8)
