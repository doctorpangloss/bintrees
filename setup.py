#!/usr/bin/env python
#coding:utf-8
# Author:  mozman
# to build c-extension:
# setup.py build_ext --inplace

import os
from distutils.core import setup
from distutils.extension import Extension
from Cython.Distutils import build_ext

ext_modules = [Extension("bintrees.cbintree", ["src/ctrees.c", "src/cbintree.pyx"]),
               Extension("bintrees.crbtree", ["src/ctrees.c", "src/crbtree.pyx"]),
               Extension("bintrees.cavltree", ["src/ctrees.c", "src/cavltree.pyx"]),
               Extension("bintrees.cbintree2", ["src/ctrees.c", "src/cbintree2.pyx"])]
def read(fname):
    return open(os.path.join(os.path.dirname(__file__), fname)).read()

setup(
    name = 'bintrees',
    version='0.3.0',
    description='Package provides Binary-, RedBlack- and AVL-Trees in Python and Cython.',
    author='mozman',
    url='http://bitbucket.org/mozman/bintrees',
    download_url='http://bitbucket.org/mozman/bintrees/downloads',
    author_email='mozman@gmx.at',
    cmdclass = {'build_ext': build_ext},
    ext_modules = ext_modules,
    packages=['bintrees'],
    requires=['cython'],
    long_description=read('README.txt'),
    platforms="OS Independent",
    license="GPLv3",
    classifiers=[
    "Development Status :: 3 - Alpha",
    "License :: OSI Approved :: GNU General Public License (GPL)",
    "Operating System :: OS Independent",
    "Programming Language :: Python :: 2.6",
    "Intended Audience :: Developers",
    "Topic :: Software Development :: Libraries :: Python Modules",
    ]
)
