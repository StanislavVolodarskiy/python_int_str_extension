#define PY_SSIZE_T_CLEAN
#include <Python.h>

#define SIGCHECK(PyTryBlock)                    \
    do {                                        \
        if (PyErr_CheckSignals()) PyTryBlock    \
    } while(0)

static int
declong_increment(PyLongObject *a, PyLongObject *b)
{
    if (Py_SIZE(a) < 0 || Py_SIZE(b) < 0) {
        PyErr_SetString(PyExc_ValueError, "negative argument");
        return -1;
    }

    PyErr_BadInternalCall();
    return -1;
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

    Py_SIZE(b) = (Py_SIZE(a) < 0) ? -size : size;

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

static PyObject *
str_to_int(PyObject *self, PyObject *args)
{
    const char *string;

    if (!PyArg_ParseTuple(args, "s", &string)) {
        return NULL;
    }
    return PyLong_FromString(string, NULL, 10);
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
increment_decint(PyObject *self, PyObject *args)
{
    PyObject *n;

    if (!PyArg_ParseTuple(args, "O!", &PyLong_Type, &n)) {
        return NULL;
    }

    return long_to_decimal_string(n);
}

static PyMethodDef methods[] = {
    {"str_to_decint", str_to_decint, METH_VARARGS, "str to decint"},
    {"decint_to_str", decint_to_str, METH_VARARGS, "decint to str"},
    {"str_to_int", str_to_int, METH_VARARGS, "str to int"},
    {"int_to_str", int_to_str, METH_VARARGS, "int to str"},
    {"increment_decint", increment_decint, METH_VARARGS, "increment decint by another decint"},
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
