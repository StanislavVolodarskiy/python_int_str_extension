from distutils.core import setup, Extension

module1 = Extension('int_str', sources = ['int_str.c'])

setup(
    name='int_str',
    version='1.0',
    description='This is a int-to-str, str-to-int conversion package',
    ext_modules=[module1]
)
