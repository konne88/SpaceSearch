<img src="https://raw.githubusercontent.com/konne88/SpaceSearch/master/logo/logo.png" width="25px"> Space Search
================

### Getting Started with SpaceSearch

SpaceSearch is a Coq library that enables the verification of solver aided
tools. 

[Docker][docker] is the most reliable way to build SpaceSearch. To build
SpaceSearch and all its dependencies run (running this command for the first time
may take an hour):

    docker build -t ss .

You can check that SpaceSearch built correctly by running an example application
that solves the [n-queens][queens] problem:

    docker run ss ss/queens.rkt 1

Note that this example implementation is currently extreamly inefficient, and
will take a very long time to return an answer for any number higher than 3.

[queens]: https://en.wikipedia.org/wiki/Eight_queens_puzzle 
[docker]: https://docs.docker.com/engine/installation/

### Developing SpaceSearch

You can also use Docker to start a SpaceSearch development environment that has
all the right dependencies setup: 

    docker rm -f ss; docker run --name ss -v $(pwd):/ss -ti ss

Running the above command starts a shell in the development environment. You can
build the SpaceSearch project with:

    make -C /ss example

From another terminal, you can connect to the development environment with your local emacs installation:

    emacs /docker:ss:/ss/src/coq/SpaceSearch.v

If your docker instance runs on another machine, you can connect to it with:

    emacs "/ssh:user@machine|docker:ss:/ss/src/coq/SpaceSearch.v"

Make sure your emacs has `ProofGeneral` and `docker-tramp` installed, and 
`enable-remote-dir-locals` must be set.
