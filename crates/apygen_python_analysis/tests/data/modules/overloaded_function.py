from typing import overload


@overload
def add(x: int, y: int) -> int: ...


@overload
def add(x: float, y: float) -> float: ...


def add(x: int | float, y: int | float) -> int | float:  # TODO: fix the test
    return x + y
