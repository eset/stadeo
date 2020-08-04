# -*- encoding: utf8 -*-
#
# Copyright (c) 2020 ESET spol. s r.o.
# Author: Vladislav Hrčka <vladislav.hrcka@eset.com>
# See LICENSE file for redistribution.

from setuptools import setup

setup(
    name='stadeo',
    version='0.0.1',
    packages=['stadeo', 'stadeo.cff', 'stadeo.utils', 'stadeo.string'],
    url='https://github.com/eset/stadeo',
    license='BSD',
    author='Vladislav Hrčka',
    author_email='vladislav.hrcka@eset.com',
    description='Stadeo is a set of tools for control-flow-flattening and string deobfuscation',
    classifiers=[
        "Development Status :: 5 - Production/Stable",
        "Environment :: Console",
        "License :: OSI Approved :: BSD License",
        "Programming Language :: Python :: 3",
    ],
    install_requires=[
        'z3-solver==4.8.7.0',
        'sortedcontainers',
        'rpyc',
        'miasm @ git+https://github.com/cea-sec/miasm@master',
    ],
    keywords=[
        "reverse engineering",
        "symbolic execution",
        "deobfuscation",
        "control flow flattening",
        "string obfuscation",
        "Stantinko",
        "Emotet",
    ],
)
