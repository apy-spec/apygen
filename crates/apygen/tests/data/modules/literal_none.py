none_value = None

bool_none = bool(None)

not_none = not None

try:
    pos_none = +None
except TypeError:
    # TODO: improve when exceptions are implemented
    pass

try:
    neg_none = -None
except TypeError:
    # TODO: improve when exceptions are implemented
    pass

try:
    invert_none = ~None
except TypeError:
    # TODO: improve when exceptions are implemented
    pass
