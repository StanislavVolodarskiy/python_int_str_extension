import sys
from int_str import (
    str_to_int,
    int_to_str,
    str_to_decint,
    decint_to_str,
    decint_add,
    decint_mul
)


def get_shift():
    p = 0
    while True:
        n = 10 ** p
        if str_to_decint(str(n)) != n:
            return p
        p += 1


def test_str_to_int():
    for i in tuple(range(100)) + tuple(9 ** 9 ** p for p in range(6)):
        assert str_to_int(str(i)) == i


def test_int_to_str():
    for i in tuple(range(100)) + tuple(9 ** 9 ** p for p in range(6)):
        assert int_to_str(i) == str(i)


def test_shift():
    if sys.int_info.bits_per_digit == 15:
        expected_shift = 4
    elif sys.int_info.bits_per_digit == 30:
        expected_shift = 9
    else:
        assert False
    assert get_shift() == expected_shift


def test_decint():

    def check(s):
        # print('checking', s)
        assert s == decint_to_str(str_to_decint(s))

    for n in range(100):
        check(str(n))

    check('12345678901234567890')

    n = 10 ** get_shift()
    assert str_to_decint(str(n - 1)) == n - 1
    assert str_to_decint(str(n)) > n

    check(str(n - 1))
    check(str(n))

    for m in range(10):
        check(str(10 ** (m * get_shift()) - 1))
        check(str(10 ** (m * get_shift())))


def test_decint_add():
    n = 10 ** get_shift()
    n1 = str_to_decint(str(n - 1))
    n2 = str_to_decint(str(1))
    assert decint_add(n1, n2) == str_to_decint(str(n))


def test_decint_mul():
    n = 10 ** get_shift()
    n1 = str_to_decint(str(n // 2))
    n2 = str_to_decint(str(2))
    assert decint_mul(n1, n2) == str_to_decint(str(n))
