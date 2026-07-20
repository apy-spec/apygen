class Point2D:
    x: int
    y: int

    def __init__(self, x: int, y: int) -> None:
        self.x = x
        self.y = y


class Point3D(Point2D):
    z: int

    def __init__(self, x: int, y: int, z: int) -> None:
        super().__init__(x, y)
        self.z = z


a: int = 3
b: int = 4
c: int = 5

point = Point3D(a, b, c)

point_x = point.x
point_y = point.y
point_z = point.z
