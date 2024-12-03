# Blowing-up-toric-surfaces

This library provides a set of functions to work with toric surfaces in the Magma computational algebra system. The library includes functionality for reordering rays, constructing toric surfaces, computing lattice ideals, and studying the Cox ring of the blow-up at a general point.

## Features

- **Reordering Rays**: Order rays of a two-dimensional fan based on their angular relationship.
- **Toric Varieties**: Create toric varieties and compute their lattice ideals.
- **Intersection Theory**: Compute intersection matrices for Weil divisors, class groups, and blow-ups.
- **Cox Ring**: Generate and analyze the Cox ring of blow-ups of projective planes.
- **Isomorphism Testing**: Check if two fans define isomorphic toric surfaces.
- **Effective Cones**: Study the pseudo-effective and pseudo-nef cones of toric surfaces.

---

## Example Usage

Here is an example of how to use the library to perform computations with a set of rays:

```magma
// Load the library
load "library.m";

// Define the rays of a fan
rays := [[1,0],[2,1],[1,1],[1,2],[0,1],[-1,2],[-1,1],[-2,1],[-1,0],[-2,-1],[-1,-1],[-1,-2],[0,-1],[1,-2],[1,-1],[2,-1]];

// Step 1: Compute the indices of subsets of rays satisfying specific conditions
S := CompIndices(rays);
lis0 := {U : U in Subsets({1..16}) | #U ge 4 and 3 notin {#(U meet V) : V in S}};

// Step 2: Filter subsets based on inclusion relations
lis1 := lis0;
for U in lis0 do
 lis1 := lis1 diff {V : V in lis1 | V subset U and V ne U};
end for;

// Step 3: Reorder rays in each subset
lis1 := [Reorder([rays[i] : i in U]) : U in lis1];
ll := {lis1[1]};
for i in [1..#lis1] do
 ra := lis1[i];
 if not &or[IsIsom(ra,u) : u in ll] then Include(~ll,ra); 
 end if;
end for;

// Step 4: Extract unique subsets of rays
lis := [Sort([Position(rays,u[i]) : i in [1..#u]]) : u in ll];

// Test if the Cox ring of each configuration is generated in multiplicity one
for R in ll do
 TestMultOne(R);
end for;

// Step 5: Compute Cox ring generators and test if the fan corresponds to a Mori dream space
ra := [rays[2*i] : i in [1..8]];
GensUpTo(ra,2);
IsMDS(ra,2);
