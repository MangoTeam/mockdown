from setuptools import setup

from os import path
project_dir = path.abspath(path.dirname(__file__))
with open(path.join(project_dir, 'README.md'), encoding='utf-8') as f:
    long_description = f.read()

setup(
    name='mockdown',
    version='0.0.1',
    packages=['mockdown'],
    url='https://github.com/MangoTeam/mockdown',
    license='MIT',

    author='Dylan A. Lukes',
    author_email='dlukes@eng.ucsd.edu',
    description='Generating constraint-based layouts from examples.',

    long_description=long_description,
    long_description_content_type='text/markdown',

    install_requires=['burdock'],
    include_package_data=True
)
