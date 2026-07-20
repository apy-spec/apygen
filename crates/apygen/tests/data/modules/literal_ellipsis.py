ellipsis_value = ...

bool_ellipsis = bool(...)

not_ellipsis = not ...

try:
    pos_ellipsis = +...
except TypeError:
    # TODO: improve when exceptions are implemented
    pass

try:
    neg_ellipsis = -...
except TypeError:
    # TODO: improve when exceptions are implemented
    pass

try:
    invert_ellipsis = ~...
except TypeError:
    # TODO: improve when exceptions are implemented
    pass
