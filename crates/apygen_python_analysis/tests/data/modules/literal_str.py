empty_str = ""
single_str = "a"
multiple_str = "test"

bool_empty_str = bool(empty_str)
bool_single_str = bool(single_str)
bool_multiple_str = bool(multiple_str)

not_empty_str = not empty_str
not_single_str = not single_str
not_multiple_str = not multiple_str

try:
    pos_empty_str = +empty_str
except TypeError:
    # TODO: improve when exceptions are implemented
    pass

try:
    neg_empty_str = -empty_str
except TypeError:
    # TODO: improve when exceptions are implemented
    pass

try:
    invert_empty_str = ~empty_str
except TypeError:
    # TODO: improve when exceptions are implemented
    pass

add_single_str_multiple_str = single_str + multiple_str

try:
    sub_single_str_multiple_str = single_str - multiple_str
except TypeError:
    # TODO: improve when exceptions are implemented
    pass

mul_empty_str_zero = empty_str * 0
mul_single_str_zero = single_str * 0
mul_multiple_str_zero = multiple_str * 0
rmul_empty_str_zero = 0 * empty_str
rmul_single_str_zero = 0 * single_str
rmul_multiple_str_zero = 0 * multiple_str
mul_empty_str_one = empty_str * 1
mul_single_str_one = single_str * 1
mul_multiple_str_one = multiple_str * 1
rmul_empty_str_one = 1 * empty_str
rmul_single_str_one = 1 * single_str
rmul_multiple_str_one = 1 * multiple_str
mul_empty_str_two = empty_str * 2
mul_single_str_two = single_str * 2
mul_multiple_str_two = multiple_str * 2
rmul_empty_str_two = 2 * empty_str
rmul_single_str_two = 2 * single_str
rmul_multiple_str_two = 2 * multiple_str
