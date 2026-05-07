empty_bytes = b""
single_bytes = b"a"
multiple_bytes = b"test"

bool_empty_bytes = bool(empty_bytes)
bool_single_bytes = bool(single_bytes)
bool_multiple_bytes = bool(multiple_bytes)

not_empty_bytes = not empty_bytes
not_single_bytes = not single_bytes
not_multiple_bytes = not multiple_bytes

try:
    pos_empty_bytes = +empty_bytes
except TypeError:
    # TODO: improve when exceptions are implemented
    pass

try:
    neg_empty_bytes = -empty_bytes
except TypeError:
    # TODO: improve when exceptions are implemented
    pass

try:
    invert_empty_bytes = ~empty_bytes
except TypeError:
    # TODO: improve when exceptions are implemented
    pass

add_single_bytes_multiple_bytes = single_bytes + multiple_bytes

try:
    sub_single_bytes_multiple_bytes = single_bytes - multiple_bytes
except TypeError:
    # TODO: improve when exceptions are implemented
    pass

mul_empty_bytes_zero = empty_bytes * 0
mul_single_bytes_zero = single_bytes * 0
mul_multiple_bytes_zero = multiple_bytes * 0
rmul_empty_bytes_zero = 0 * empty_bytes
rmul_single_bytes_zero = 0 * single_bytes
rmul_multiple_bytes_zero = 0 * multiple_bytes
mul_empty_bytes_one = empty_bytes * 1
mul_single_bytes_one = single_bytes * 1
mul_multiple_bytes_one = multiple_bytes * 1
rmul_empty_bytes_one = 1 * empty_bytes
rmul_single_bytes_one = 1 * single_bytes
rmul_multiple_bytes_one = 1 * multiple_bytes
mul_empty_bytes_two = empty_bytes * 2
mul_single_bytes_two = single_bytes * 2
mul_multiple_bytes_two = multiple_bytes * 2
rmul_empty_bytes_two = 2 * empty_bytes
rmul_single_bytes_two = 2 * single_bytes
rmul_multiple_bytes_two = 2 * multiple_bytes
