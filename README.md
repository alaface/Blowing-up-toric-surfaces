# Blowing-up-toric-surfaces

This library provides a set of functions to work with toric surfaces in the Magma computational algebra system. The library includes functionality for reordering rays, constructing toric surfaces, computing lattice ideals, and studying the Cox ring of the blow-up at a general point.

## Functions Overview

- **Fan Manipulation**
  - `Reorder`: Reorders rays based on angular relationships.
  - `NextOne`: Finds the next ray in a sequence based on orientation.

- **Toric Geometry**
  - `ToricFromRays`: Constructs a toric variety from rays.
  - `LatticeIdeal`: Computes the lattice ideal of a toric variety.

- **Cox Ring Analysis**
  - `MultOneIdeal`: Computes the saturation of an ideal up to multiplicity one.
  - `GensUpTo`: Generates classes of the Cox ring up to a specified multiplicity.
  - `IsMDS`: Tests if the fan defines a Mori dream space.

- **Intersection Theory**
  - `IntMatWeil`: Computes the intersection matrix for Weil divisors.
  - `IntMatCl`: Computes the intersection matrix for the class group.
  - `IntMatBl`: Computes the intersection matrix for the blow-up of a projective plane.

- **Other Utilities**
  - `IsIsom`: Checks isomorphism between two fans.
  - `CompIndices`: Identifies subsets of rays satisfying specific combinatorial conditions.

---

## Dependencies

- **Magma**: The library is designed to be used with the Magma computational algebra system.

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
