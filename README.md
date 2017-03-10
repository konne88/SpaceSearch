<img src="https://raw.githubusercontent.com/konne88/SpaceSearch/master/logo/logo.png" width="25px"> Space Search
================

### Getting Started with SpaceSearch

Many effective verification tools build on automated solvers. These tools reduce
problems in an application domain (ranging from data-race detection to compiler
optimization validation) to the domain of a highly optimized solver like Z3.
However, this reduction is rarely formally verified in practice, leaving the
end-to-end soundness of the tool in question.  SpaceSearch is a library to
verify such tools by means of a proof assistant. 

[Docker][docker] is the most reliable way to build SpaceSearch. To build
SpaceSearch and all its dependencies run (running this command for the first time
may take an hour):

    docker build -t ss .

You can check that SpaceSearch built correctly by running an example application
that solves the [n-queens][queens] problem:

    docker run ss ss/queens.rkt 8

[queens]: https://en.wikipedia.org/wiki/Eight_queens_puzzle 
[docker]: https://docs.docker.com/engine/installation/

### Developing SpaceSearch

You can also use Docker to start a SpaceSearch development environment that has
all the right dependencies setup: 

    docker rm -f ss; docker run --name ss --entrypoint /bin/bash -v $(pwd):/ss -ti ss

If you like the `fish` shell (i do) run:

    docker rm -f ss; docker run --name ss --entrypoint /usr/bin/fish -v (pwd):/ss -ti ss

Running the above command starts a shell in the development environment. You can
build the SpaceSearch project with:

    make -C /ss examples

From another terminal, you can connect to the development environment with your local emacs installation:

    emacs /docker:ss:/ss/src/coq/SpaceSearch.v

If your docker instance runs on another machine, you can connect to it with:

    emacs "/ssh:user@machine|docker:ss:/ss/src/coq/SpaceSearch.v"

Make sure your emacs has `ProofGeneral` and `docker-tramp` installed, and 
`enable-remote-dir-locals` must be set.
