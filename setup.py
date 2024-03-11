from setuptools import setup

setup(
    install_requires=[
        "Cython==3.0.8",
    "dd @ git+https://github.com/masinag/dd.git@main"
    "pydot==1.4.2",
    "PySDD==0.2.11",
    "PySMT==0.9.6.dev53",
    "pywmi @ git+https://github.com/weighted-model-integration/pywmi@1c642518c75211d909fcfeb940085d6f12c1918f",
    ]
)