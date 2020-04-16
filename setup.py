from setuptools import setup, find_packages

from os import path

project_dir = path.abspath(path.dirname(__file__))
with open(path.join(project_dir, 'README.md'), encoding='utf-8') as f:
    long_description = f.read()

setup(
    name='mockdown',
    version='0.0.1',
    packages=find_packages('src'),
    package_dir={'': 'src'},
    url='https://github.com/MangoTeam/mockdown',
    license='MIT',

    author='Dylan A. Lukes',
    author_email='dlukes@eng.ucsd.edu',
    description='Generating constraint-based layouts from examples.',

    long_description=long_description,
    long_description_content_type='text/markdown',

    install_requires=[
        'click',
        'intervaltree',
        'more-itertools',
        'pyswip',
        'uvicorn',
        'starlette',
        'aiofiles',
        'timing-asgi',
        'z3-solver',
        'pandas'
    ],

    setup_requires=[
        'pytest-runner',
    ],

    include_package_data=True,

    entry_points='''
        [console_scripts]
        mockdown=mockdown.cli:cli
    ''',
)
