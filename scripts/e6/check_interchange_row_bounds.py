"""Test hereditary rigid labels and conserved row bounds on doubly subdivided cylinders."""

from itertools import product

from interchange_cylinders import compose
from interchange_gray_composition import check_stationary
from interchange_subdivision import cylinder_data, stack_image


def moving_halves(p, slot, cut, end):
    disk, left, right = cylinder_data(p, slot)

    def part(cell, lo, hi):
        return stack_image(cell, p, slot, lo, hi)

    if slot == 0:
        return (compose(part(disk, 0, cut), part(right, cut, end), p - 1),
                compose(part(left, 0, cut), part(disk, cut, end), p - 1))
    return (compose(part(left, 0, cut), part(disk, cut, end), p - 1),
            compose(part(disk, 0, cut), part(right, cut, end), p - 1))


def rigid_labels(table, slot):
    # On this shape the only high rigid inputs are named moving globes.
    # The tableau's basis pairs independently identify the globes used.
    return {pair[slot] for row in table for chain in row for pair in chain
            if pair[slot][0] >= 4}


def face_closure(keys, p):
    closure = set(keys)
    for rank in range(p, 4, -1):
        for _, label in [key for key in closure if key[0] == rank]:
            faces = (label, label + 1) if rank == p else (0, 1)
            closure.update((rank - 1, i) for i in faces)
    return closure


def verify(p, slot, moving, stationary, cut, axis):
    disk = cylinder_data(p, slot)[0]
    direct = stack_image(stack_image(disk, p, slot, 0, moving),
                         1, 1 - slot, 0, stationary)
    if axis == 'moving':
        parts = [stack_image(piece, 1, 1 - slot, 0, stationary)
                 for piece in moving_halves(p, slot, cut, moving)]
        hidden = (p - 1, cut)
        assert hidden not in rigid_labels(direct, slot)
        assert any(hidden in rigid_labels(piece, slot) for piece in parts)
    else:
        parts = [stack_image(piece, p, slot, 0, moving)
                 for piece in check_stationary(p, slot, cut, stationary)]

    first, second = parts
    assert compose(first, second, p) == direct
    keys = face_closure(rigid_labels(direct, slot), p)
    child_keys = set().union(*(face_closure(rigid_labels(piece, slot), p) for piece in parts))
    assert keys == child_keys

    # In these particular hom rows every basis summand has unit charge.
    # The preceding cylinder contributes one per stationary edge, the pure
    # insertion one per moving globe. Test the interior face as well.
    for cell in (direct, first, second):
        assert all(len(chain) == moving + stationary for chain in cell[p])
        assert all(len(chain) <= moving * stationary for chain in cell[p + 1])
    assert len(first[-1][0]) + len(second[-1][0]) == len(direct[-1][0]) == moving * stationary


if __name__ == '__main__':
    total = 0
    for p, slot, moving, stationary in product(range(5, 11), range(2), range(2, 5), range(2, 5)):
        for axis, width in (('moving', moving), ('stationary', stationary)):
            for cut in range(1, width):
                verify(p, slot, moving, stationary, cut, axis)
                total += 1
    print(f'{total} two-axis stack tests preserved the face-closed rigid labels, '
          'top weight, and weights of both endpoints and the intermediate row.')
