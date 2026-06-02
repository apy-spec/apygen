class Point:
    x: int
    y: int

    def __init__(self, x: int, y: int) -> None:
        self.x = x
        self.y = y

a: int = 3
b: int = 4

point = Point(a, b)

point_x = point.x
point_y = point.y
