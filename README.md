This is a library for working with finite graphs, including a brute force decision procedure for finding a path between two nodes in [`Data.Graph.Path.Search`](src/Data/Graph/Path/Search.agda).

# How to build
Building requires the following libraries in an Agda [`libraries` file](http://agda.readthedocs.io/en/v2.5.3/tools/package-system.html):
- [Agda standard library](http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Libraries.StandardLibrary) under the name `standard-libarary`
- https://github.com/kcsmnt0/finite under the name `finite`

This code has been tested against Agda version 2.5.4 and standard library version 0.16.
