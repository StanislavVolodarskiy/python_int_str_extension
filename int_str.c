#define PY_SSIZE_T_CLEAN
#define Py_BUILD_CORE
#include <Python.h>
#include <internal/pycore_global_objects.h>
#include <internal/pycore_object.h>
#include <internal/pycore_long.h>
#include <ceval.h>

#include <stddef.h>

static inline void
_Py_DECREF_INT(PyLongObject *op)
{
    assert(PyLong_CheckExact(op));
    _Py_DECREF_SPECIALIZED((PyObject *)op, (destructor)PyObject_Free);
}

#define SIGCHECK(PyTryBlock)                    \
    do {                                        \
        if (PyErr_CheckSignals()) PyTryBlock    \
    } while(0)

static PyLongObject *
long_normalize(PyLongObject *v)
{
    Py_ssize_t j = Py_ABS(Py_SIZE(v));
    Py_ssize_t i = j;

    while (i > 0 && v->ob_digit[i-1] == 0)
        --i;
    if (i != j) {
        Py_SET_SIZE(v, (Py_SIZE(v) < 0) ? -(i) : i);
    }
    return v;
}

static PyLongObject *
declong_add(PyLongObject *a, PyLongObject *b)
{
    Py_ssize_t size_a = Py_SIZE(a);
    Py_ssize_t size_b = Py_SIZE(b);

    if (size_a < 0 || size_b < 0) {
        PyErr_SetString(PyExc_ValueError, "negative argument");
        return NULL;
    }

    PyLongObject *z;
    Py_ssize_t i;
    digit carry = 0;

    /* Ensure a is the larger of the two: */
    if (size_a < size_b) {
        { PyLongObject *temp = a; a = b; b = temp; }
        { Py_ssize_t size_temp = size_a;
            size_a = size_b;
            size_b = size_temp; }
    }
    z = _PyLong_New(size_a + 1);
    if (z == NULL)
        return NULL;
    for (i = 0; i < size_b; ++i) {
        carry += a->ob_digit[i] + b->ob_digit[i];
        z->ob_digit[i] = carry % _PyLong_DECIMAL_BASE;
        carry /= _PyLong_DECIMAL_BASE;
    }
    for (; i < size_a; ++i) {
        carry += a->ob_digit[i];
        z->ob_digit[i] = carry % _PyLong_DECIMAL_BASE;
        carry /= _PyLong_DECIMAL_BASE;
    }
    z->ob_digit[i] = carry;
    return long_normalize(z);
}

static PyLongObject *
declong_mul(PyLongObject *a, PyLongObject *b)
{
    Py_ssize_t size_a = Py_SIZE(a);
    Py_ssize_t size_b = Py_SIZE(b);

    if (size_a < 0 || size_b < 0) {
        PyErr_SetString(PyExc_ValueError, "negative argument");
        return NULL;
    }

    PyLongObject *z;
    Py_ssize_t i;

    z = _PyLong_New(size_a + size_b);
    if (z == NULL)
        return NULL;

    memset(z->ob_digit, 0, Py_SIZE(z) * sizeof(digit));
    if (a == b) {
        /* Efficient squaring per HAC, Algorithm 14.16:
         * http://www.cacr.math.uwaterloo.ca/hac/about/chap14.pdf
         * Gives slightly less than a 2x speedup when a == b,
         * via exploiting that each entry in the multiplication
         * pyramid appears twice (except for the size_a squares).
         */
        for (i = 0; i < size_a; ++i) {
            twodigits carry;
            twodigits f = a->ob_digit[i];
            digit *pz = z->ob_digit + (i << 1);
            digit *pa = a->ob_digit + i + 1;
            digit *paend = a->ob_digit + size_a;

            SIGCHECK({
                    Py_DECREF(z);
                    return NULL;
                });

            carry = *pz + f * f;
            *pz++ = (digit)(carry % _PyLong_DECIMAL_BASE);
            carry /= _PyLong_DECIMAL_BASE;
            assert(carry < _PyLong_DECIMAL_BASE);

            /* Now f is added in twice in each column of the
             * pyramid it appears.  Same as adding f<<1 once.
             */
            f <<= 1;
            while (pa < paend) {
                carry += *pz + *pa++ * f;
                *pz++ = (digit)(carry % _PyLong_DECIMAL_BASE);
                carry /= _PyLong_DECIMAL_BASE;
                assert(carry <= ((_PyLong_DECIMAL_BASE - 1) << 1));
            }
            if (carry) {
                carry += *pz;
                *pz++ = (digit)(carry % _PyLong_DECIMAL_BASE);
                carry /= _PyLong_DECIMAL_BASE;
            }
            if (carry)
                *pz += (digit)(carry % _PyLong_DECIMAL_BASE);
            assert(carry < _PyLong_DECIMAL_BASE);
        }
    }
    else {      /* a is not the same as b -- gradeschool int mult */
        for (i = 0; i < size_a; ++i) {
            twodigits carry = 0;
            twodigits f = a->ob_digit[i];
            digit *pz = z->ob_digit + i;
            digit *pb = b->ob_digit;
            digit *pbend = b->ob_digit + size_b;

            SIGCHECK({
                    Py_DECREF(z);
                    return NULL;
                });

            while (pb < pbend) {
                carry += *pz + *pb++ * f;
                *pz++ = (digit)(carry % _PyLong_DECIMAL_BASE);
                carry /= _PyLong_DECIMAL_BASE;
                assert(carry < _PyLong_DECIMAL_BASE);
            }
            if (carry)
                *pz += (digit)(carry % _PyLong_DECIMAL_BASE);
            assert(carry < _PyLong_DECIMAL_BASE);
        }
    }
    return long_normalize(z);
}

/* Convert an integer to a declong.  A declong is a PyLongObject
   storing its value in _PyLong_DECIMAL_BASE base. */

static PyLongObject *
long_to_declong(PyLongObject *a)
{
    PyLongObject *b;
    Py_ssize_t size, size_a, i, j;
    digit *pout, *pin;
    int d;

    size_a = Py_ABS(Py_SIZE(a));

    /* quick and dirty upper bound for the number of digits
       required to express a in base _PyLong_DECIMAL_BASE:

         #digits = 1 + floor(log2(a) / log2(_PyLong_DECIMAL_BASE))

       But log2(a) < size_a * PyLong_SHIFT, and
       log2(_PyLong_DECIMAL_BASE) = log2(10) * _PyLong_DECIMAL_SHIFT
                                  > 3.3 * _PyLong_DECIMAL_SHIFT

         size_a * PyLong_SHIFT / (3.3 * _PyLong_DECIMAL_SHIFT) =
             size_a + size_a / d < size_a + size_a / floor(d),
       where d = (3.3 * _PyLong_DECIMAL_SHIFT) /
                 (PyLong_SHIFT - 3.3 * _PyLong_DECIMAL_SHIFT)
    */
    d = (33 * _PyLong_DECIMAL_SHIFT) /
        (10 * PyLong_SHIFT - 33 * _PyLong_DECIMAL_SHIFT);
    assert(size_a < PY_SSIZE_T_MAX / 2);
    size = 1 + size_a + size_a / d;
    b = _PyLong_New(size);
    if (b == NULL)
        return NULL;

    /* convert array of base _PyLong_BASE digits in pin to an array of
       base _PyLong_DECIMAL_BASE digits in pout, following Knuth (TAOCP,
       Volume 2 (3rd edn), section 4.4, Method 1b). */
    pin = a->ob_digit;
    pout = b->ob_digit;
    size = 0;
    for (i = size_a; --i >= 0; ) {
        digit hi = pin[i];
        for (j = 0; j < size; j++) {
            twodigits z = (twodigits)pout[j] << PyLong_SHIFT | hi;
            hi = (digit)(z / _PyLong_DECIMAL_BASE);
            pout[j] = (digit)(z - (twodigits)hi *
                              _PyLong_DECIMAL_BASE);
        }
        while (hi) {
            pout[size++] = hi % _PyLong_DECIMAL_BASE;
            hi /= _PyLong_DECIMAL_BASE;
        }
        /* check for keyboard interrupt */
        SIGCHECK({
                Py_DECREF(b);
                return NULL;
            });
    }

    Py_SET_SIZE(b, (Py_SIZE(a) < 0) ? -size : size);

    return b;
}

/* Convert an declong to a base 10 string.  Returns a new non-shared
   string.  (Return value is non-shared so that callers can modify the
   returned value if necessary.) */

static int
declong_to_decimal_string_internal(PyLongObject *a,
                                   PyObject **p_output)
{
    PyObject *str;
    Py_ssize_t size, strlen, i, j;
    digit *pout, rem, tenpow;
    int negative;
    enum PyUnicode_Kind kind;

    pout = a->ob_digit;

    negative = Py_SIZE(a) < 0;

    /* calculate exact length of output string */
    size = Py_ABS(Py_SIZE(a));
    if (size == 0) {
        strlen = 1;
    }
    else {
        strlen = negative + 1 + (size - 1) * _PyLong_DECIMAL_SHIFT;
        tenpow = 10;
        rem = pout[size-1];
        while (rem >= tenpow) {
            tenpow *= 10;
            strlen++;
        }
    }

    str = PyUnicode_New(strlen, '9');
    if (str == NULL) {
        return -1;
    }
    kind = PyUnicode_KIND(str);

#define WRITE_DIGITS(p)                                               \
    do {                                                              \
        /* pout[0] through pout[size-2] contribute exactly            \
           _PyLong_DECIMAL_SHIFT digits each */                       \
        for (i=0; i < size - 1; i++) {                                \
            rem = pout[i];                                            \
            for (j = 0; j < _PyLong_DECIMAL_SHIFT; j++) {             \
                *--p = '0' + rem % 10;                                \
                rem /= 10;                                            \
            }                                                         \
        }                                                             \
        /* pout[size-1]: always produce at least one decimal digit */ \
        rem = pout[i];                                                \
        do {                                                          \
            *--p = '0' + rem % 10;                                    \
            rem /= 10;                                                \
        } while (rem != 0);                                           \
                                                                      \
        /* and sign */                                                \
        if (negative)                                                 \
            *--p = '-';                                               \
    } while (0)

#define WRITE_UNICODE_DIGITS(TYPE)                                    \
    do {                                                              \
        p = (TYPE*)PyUnicode_DATA(str) + strlen;                      \
                                                                      \
        if (size == 0)                                                \
            *--p = '0';                                               \
        else                                                          \
            WRITE_DIGITS(p);                                          \
                                                                      \
        /* check we've counted correctly */                           \
        assert(p == (TYPE*)PyUnicode_DATA(str));                      \
    } while (0)

    /* fill the string right-to-left */
    if (kind == PyUnicode_1BYTE_KIND) {
        Py_UCS1 *p;
        WRITE_UNICODE_DIGITS(Py_UCS1);
    }
    else if (kind == PyUnicode_2BYTE_KIND) {
        Py_UCS2 *p;
        WRITE_UNICODE_DIGITS(Py_UCS2);
    }
    else {
        Py_UCS4 *p;
        assert (kind == PyUnicode_4BYTE_KIND);
        WRITE_UNICODE_DIGITS(Py_UCS4);
    }
#undef WRITE_DIGITS
#undef WRITE_UNICODE_DIGITS

    assert(_PyUnicode_CheckConsistency(str, 1));
    *p_output = (PyObject *)str;

    return 0;
}

/* Convert an integer to a base 10 string.  Returns a new non-shared
   string.  (Return value is non-shared so that callers can modify the
   returned value if necessary.) */

static int
long_to_decimal_string_internal(PyObject *a,
                                PyObject **p_output)
{
    PyLongObject *declong;
    int result;

    if (a == NULL || !PyLong_Check(a)) {
        PyErr_BadInternalCall();
        return -1;
    }
    declong = long_to_declong((PyLongObject *)a);
    if (declong == NULL)
        return -1;

    result = declong_to_decimal_string_internal(declong, p_output);

    Py_DECREF(declong);

    return result;
}

static PyObject *
long_to_decimal_string(PyObject *aa)
{
    PyObject *v;
    if (long_to_decimal_string_internal(aa, &v) == -1)
        return NULL;
    return v;
}

static PyObject *
str_to_decint(PyObject *self, PyObject *args)
{
    const char *string;
    Py_ssize_t slen;
    Py_ssize_t size;
    PyLongObject *n;
    Py_ssize_t k;
    const char *pin;
    digit *pout;

    if (!PyArg_ParseTuple(args, "s", &string)) {
        return NULL;
    }

    slen = strlen(string);
    if (slen == 0) {
        PyErr_SetString(PyExc_ValueError, "empty string");
        return NULL;
    }
    if (slen > 1 && string[0] == '0') {
        PyErr_SetString(PyExc_ValueError, "first digit is zero");
        return NULL;
    }

    if (slen == 1 && string[0] == '0') {
        size = 0;
    }
    else {
        size = (slen + _PyLong_DECIMAL_SHIFT - 1) / _PyLong_DECIMAL_SHIFT;
    }

    n = _PyLong_New(size);
    if (n == NULL)
        return NULL;
    if (size == 0)
        return (PyObject *) n;

    assert(size > 0);
    pin = string;
    pout = n->ob_digit + size;

    k = (slen - 1) % _PyLong_DECIMAL_SHIFT + 1;
    while (*pin != '\0') {
        Py_ssize_t i;
        digit d;

        d = 0;
        for (i = 0; i < k; ++i) {
            char c = *pin++;
            assert(c != '\0');
            if (c < '0' || '9' < c) {
                Py_DECREF(n);
                PyErr_SetString(PyExc_ValueError, "invalid character");
                return NULL;
            }
            d = 10 * d + (c - '0');
        }
        *(--pout) = d;
        k = _PyLong_DECIMAL_SHIFT;
    }
    assert(pout == n->ob_digit);

    return (PyObject *) n;
}

static PyObject *
decint_to_str(PyObject *self, PyObject *args)
{
    PyObject *nn;
    PyObject *str;
    int result;

    if (!PyArg_ParseTuple(args, "O!", &PyLong_Type, &nn)) {
        return NULL;
    }

    result = declong_to_decimal_string_internal((PyLongObject *) nn, &str);

    return (result == 0) ? str : NULL;
}

#define MAX_LONG_DIGITS \
    ((PY_SSIZE_T_MAX - offsetof(PyLongObject, ob_digit))/sizeof(digit))

/* Is this PyLong of size 1, 0 or -1? */
#define IS_MEDIUM_VALUE(x) (((size_t)Py_SIZE(x)) + 1U < 3U)

#define IS_SMALL_INT(ival) (-_PY_NSMALLNEGINTS <= (ival) && (ival) < _PY_NSMALLPOSINTS)

static PyLongObject *
maybe_small_long(PyLongObject *v)
{
    if (v && IS_MEDIUM_VALUE(v)) {
        stwodigits ival = ((stwodigits)Py_SIZE(v)) * v->ob_digit[0];
        if (IS_SMALL_INT(ival)) {
            _Py_DECREF_INT(v);
            PyLongObject *w = &_Py_SINGLETON(small_ints)[_PY_NSMALLNEGINTS + ival];
            Py_INCREF(w);
            return w;
        }
    }
    return v;
}

static double log_base_BASE_10 = 0;
static int convwidth_base_10 = 0;
static twodigits convmultmax_base_10 = 0;

static PyLongObject *
fromDigits(const char *str, Py_ssize_t digits)
{
    PyLongObject *z = NULL;
    twodigits convmult;
    Py_ssize_t size_z;
    twodigits c;           /* current input character */
    int i;
    digit *pz, *pzstop;

    /* Create an int object that can contain the largest possible
     * integer with this base and length.  Note that there's no
     * need to initialize z->ob_digit -- no slot is read up before
     * being stored into.
     */
    double fsize_z = (double)digits * log_base_BASE_10 + 1.0;
    if (fsize_z > (double)MAX_LONG_DIGITS) {
        /* The same exception as in _PyLong_New(). */
        PyErr_SetString(PyExc_OverflowError,
                        "too many digits in integer");
        return NULL;
    }
    size_z = (Py_ssize_t)fsize_z;
    /* Uncomment next line to test exceedingly rare copy code */
    /* size_z = 1; */
    assert(size_z > 0);
    z = _PyLong_New(size_z);
    if (z == NULL) {
        return NULL;
    }
    Py_SET_SIZE(z, 0);

    /* `convwidth_base_10` consecutive input digits are treated as a single
     * digit in base `convmultmax_base_10`.
     */

    /* Work ;-) */
    while (digits > 0) {
        if (*str == '_') {
            str++;
            continue;
        }
        /* grab up to convwidth_base_10 digits from the input string */
        c = (digit)((*str++) - '0');
        --digits;
        for (i = 1; i < convwidth_base_10 && digits > 0; ++str, --digits) {
            if (*str == '_') {
                continue;
            }
            i++;
            c = (twodigits)(c * 10 + (int)((*str) - '0'));
            assert(c < PyLong_BASE);
        }

        convmult = convmultmax_base_10;
        /* Calculate the shift only if we couldn't get
         * convwidth_base_10 digits.
         */
        if (i != convwidth_base_10) {
            convmult = 10;
            for ( ; i > 1; --i) {
                convmult *= 10;
            }
        }

        /* Multiply z by convmult, and add c. */
        pz = z->ob_digit;
        pzstop = pz + Py_SIZE(z);
        for (; pz < pzstop; ++pz) {
            c += (twodigits)*pz * convmult;
            *pz = (digit)(c & PyLong_MASK);
            c >>= PyLong_SHIFT;
        }
        /* carry off the current end? */
        if (c) {
            assert(c < PyLong_BASE);
            if (Py_SIZE(z) < size_z) {
                *pz = (digit)c;
                Py_SET_SIZE(z, Py_SIZE(z) + 1);
            }
            else {
                PyLongObject *tmp;
                /* Extremely rare.  Get more space. */
                assert(Py_SIZE(z) == size_z);
                tmp = _PyLong_New(size_z + 1);
                if (tmp == NULL) {
                    Py_DECREF(z);
                    return NULL;
                }
                memcpy(tmp->ob_digit,
                       z->ob_digit,
                       sizeof(digit) * size_z);
                Py_DECREF(z);
                z = tmp;
                z->ob_digit[size_z] = (digit)c;
                ++size_z;
            }
        }
    }
    return z;
}

static PyObject *
fromString(const char *str, char **pend)
{
    int sign = 1;
    const char *start, *orig_str = str;
    PyLongObject *z = NULL;
    PyObject *strobj;
    Py_ssize_t slen;

    while (*str != '\0' && Py_ISSPACE(*str)) {
        str++;
    }
    if (*str == '+') {
        ++str;
    }
    else if (*str == '-') {
        ++str;
        sign = -1;
    }
    if (str[0] == '_') {
        /* May not start with underscores. */
        goto onError;
    }

    start = str;
    {
/***
Binary bases can be converted in time linear in the number of digits, because
Python's representation base is binary.  Other bases (including decimal!) use
the simple quadratic-time algorithm below, complicated by some speed tricks.

First some math:  the largest integer that can be expressed in N base-B digits
is B**N-1.  Consequently, if we have an N-digit input in base B, the worst-
case number of Python digits needed to hold it is the smallest integer n s.t.

    BASE**n-1 >= B**N-1  [or, adding 1 to both sides]
    BASE**n >= B**N      [taking logs to base BASE]
    n >= log(B**N)/log(BASE) = N * log(B)/log(BASE)

The static array log_base_BASE[base] == log(base)/log(BASE) so we can compute
this quickly.  A Python int with that much space is reserved near the start,
and the result is computed into it.

The input string is actually treated as being in base base**i (i.e., i digits
are processed at a time), where two more static arrays hold:

    convwidth_base[base] = the largest integer i such that base**i <= BASE
    convmultmax_base[base] = base ** convwidth_base[base]

The first of these is the largest i such that i consecutive input digits
must fit in a single Python digit.  The second is effectively the input
base we're really using.

Viewing the input as a sequence <c0, c1, ..., c_n-1> of digits in base
convmultmax_base[base], the result is "simply"

   (((c0*B + c1)*B + c2)*B + c3)*B + ... ))) + c_n-1

where B = convmultmax_base[base].

Error analysis:  as above, the number of Python digits `n` needed is worst-
case

    n >= N * log(B)/log(BASE)

where `N` is the number of input digits in base `B`.  This is computed via

    size_z = (Py_ssize_t)((scan - str) * log_base_BASE[base]) + 1;

below.  Two numeric concerns are how much space this can waste, and whether
the computed result can be too small.  To be concrete, assume BASE = 2**15,
which is the default (and it's unlikely anyone changes that).

Waste isn't a problem:  provided the first input digit isn't 0, the difference
between the worst-case input with N digits and the smallest input with N
digits is about a factor of B, but B is small compared to BASE so at most
one allocated Python digit can remain unused on that count.  If
N*log(B)/log(BASE) is mathematically an exact integer, then truncating that
and adding 1 returns a result 1 larger than necessary.  However, that can't
happen:  whenever B is a power of 2, long_from_binary_base() is called
instead, and it's impossible for B**i to be an integer power of 2**15 when
B is not a power of 2 (i.e., it's impossible for N*log(B)/log(BASE) to be
an exact integer when B is not a power of 2, since B**i has a prime factor
other than 2 in that case, but (2**15)**j's only prime factor is 2).

The computed result can be too small if the true value of N*log(B)/log(BASE)
is a little bit larger than an exact integer, but due to roundoff errors (in
computing log(B), log(BASE), their quotient, and/or multiplying that by N)
yields a numeric result a little less than that integer.  Unfortunately, "how
close can a transcendental function get to an integer over some range?"
questions are generally theoretically intractable.  Computer analysis via
continued fractions is practical:  expand log(B)/log(BASE) via continued
fractions, giving a sequence i/j of "the best" rational approximations.  Then
j*log(B)/log(BASE) is approximately equal to (the integer) i.  This shows that
we can get very close to being in trouble, but very rarely.  For example,
76573 is a denominator in one of the continued-fraction approximations to
log(10)/log(2**15), and indeed:

    >>> log(10)/log(2**15)*76573
    16958.000000654003

is very close to an integer.  If we were working with IEEE single-precision,
rounding errors could kill us.  Finding worst cases in IEEE double-precision
requires better-than-double-precision log() functions, and Tim didn't bother.
Instead the code checks to see whether the allocated space is enough as each
new Python digit is added, and copies the whole thing to a larger int if not.
This should happen extremely rarely, and in fact I don't have a test case
that triggers it(!).  Instead the code was tested by artificially allocating
just 1 digit at the start, so that the copying code was exercised for every
digit beyond the first.
***/
        Py_ssize_t digits = 0;
        const char *scan, *lastdigit;
        char prev = 0;

        if (log_base_BASE_10 == 0.) {
            twodigits convmax = 10;
            int i = 1;

            log_base_BASE_10 = log(10.) / log((double)PyLong_BASE);
            for (;;) {
                twodigits next = convmax * 10;
                if (next > PyLong_BASE) {
                    break;
                }
                convmax = next;
                ++i;
            }
            convmultmax_base_10 = convmax;
            assert(i > 0);
            convwidth_base_10 = i;
        }

        /* Find length of the string of numeric characters. */
        scan = str;
        lastdigit = str;

        while (('0' <= *scan && *scan <= '9') || *scan == '_') {
            if (*scan == '_') {
                if (prev == '_') {
                    /* Only one underscore allowed. */
                    str = lastdigit + 1;
                    goto onError;
                }
            }
            else {
                ++digits;
                lastdigit = scan;
            }
            prev = *scan;
            ++scan;
        }
        if (prev == '_') {
            /* Trailing underscore not allowed. */
            /* Set error pointer to first underscore. */
            str = lastdigit + 1;
            goto onError;
        }

        z = fromDigits(str, digits);
        if (z != NULL) {
            str = scan;
        }
    }
    if (z == NULL) {
        return NULL;
    }
    if (str == start) {
        goto onError;
    }
    if (sign < 0) {
        Py_SET_SIZE(z, -(Py_SIZE(z)));
    }
    while (*str && Py_ISSPACE(*str)) {
        str++;
    }
    if (*str != '\0') {
        goto onError;
    }
    long_normalize(z);
    z = maybe_small_long(z);
    if (z == NULL) {
        return NULL;
    }
    if (pend != NULL) {
        *pend = (char *)str;
    }
    return (PyObject *) z;

  onError:
    if (pend != NULL) {
        *pend = (char *)str;
    }
    Py_XDECREF(z);
    slen = strlen(orig_str) < 200 ? strlen(orig_str) : 200;
    strobj = PyUnicode_FromStringAndSize(orig_str, slen);
    if (strobj == NULL) {
        return NULL;
    }
    PyErr_Format(PyExc_ValueError,
                 "invalid literal for int() with base 10: %.200R",
                 strobj);
    Py_DECREF(strobj);
    return NULL;
}

static PyObject *
str_to_int(PyObject *self, PyObject *args)
{
    const char *string;

    if (!PyArg_ParseTuple(args, "s", &string)) {
        return NULL;
    }
    return fromString(string, NULL);
}

static PyObject *
int_to_str(PyObject *self, PyObject *args)
{
    PyObject *n;

    if (!PyArg_ParseTuple(args, "O!", &PyLong_Type, &n)) {
        return NULL;
    }

    return long_to_decimal_string(n);
}

static PyObject *
decint_add(PyObject *self, PyObject *args)
{
    PyObject *a;
    PyObject *b;

    if (!PyArg_ParseTuple(args, "O!O!", &PyLong_Type, &a, &PyLong_Type, &b)) {
        return NULL;
    }

    return (PyObject *)declong_add((PyLongObject *) a, (PyLongObject *) b);
}

static PyObject *
decint_mul(PyObject *self, PyObject *args)
{
    PyObject *a;
    PyObject *b;

    if (!PyArg_ParseTuple(args, "O!O!", &PyLong_Type, &a, &PyLong_Type, &b)) {
        return NULL;
    }

    return (PyObject *)declong_mul((PyLongObject *) a, (PyLongObject *) b);
}

static PyMethodDef methods[] = {
    {"str_to_decint", str_to_decint, METH_VARARGS, "str to decint"},
    {"decint_to_str", decint_to_str, METH_VARARGS, "decint to str"},
    {"str_to_int", str_to_int, METH_VARARGS, "str to int"},
    {"int_to_str", int_to_str, METH_VARARGS, "int to str"},
    {"decint_add", decint_add, METH_VARARGS, "adds two decints"},
    {"decint_mul", decint_mul, METH_VARARGS, "muls two decints"},
    {NULL, NULL, 0, NULL}
};

static struct PyModuleDef module = {
    PyModuleDef_HEAD_INIT,
    "int_str",
    NULL, /* module doc */
    -1, /* module state size */
    methods
};

PyMODINIT_FUNC
PyInit_int_str(void)
{
    return PyModule_Create(&module);
}
