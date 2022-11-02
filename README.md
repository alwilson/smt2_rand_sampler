# SMT2 Random Sampler

Explorations in Uniform Sampling of SMT2 Constraints

## Region Sampler

This sampler uses z3 to optimize each variable for their min and max values.
Starting with this initial bounding region it can make random samples in that region.
To do this it compiles the constraints and variables into a python function.
Option to binary-search through regions, splitting them and eliminating them if z3 can't satisfy them.

### TOOD

- Split variables and constraints into separate groups if unrelated to each other
- Split regions based on hit rate and variables
- Soft constraint support, need to be able to eliminate soft-constraints for the compiled python function

### Examples
```bash
$ ./region_sampler.py -s 2 -f examples/circle.smt2
```


