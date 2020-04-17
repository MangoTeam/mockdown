from setuptools import setup

setup(
    entry_points='''
        [console_scripts]
        mockdown=mockdown.cli:cli
    ''',
)
