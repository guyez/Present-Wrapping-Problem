% pwp base case

% import for global constraints
include "globals.mzn";

% paper roll dimensions
int: w;
int: h;

% number of necessary pieces of paper to cut off
int: n;
set of int: NPIECES = 1..n;

% dimension of each piece of paper
array[NPIECES,1..2] of int: dimension;

% variables
array[NPIECES, 1..2] of var int: origin;

% useful constants 
int: x = 1;
int: y = 2;

% origins domain constraints 
constraint forall(i in NPIECES)
                    ((origin[i,x] >= 0 /\ origin[i,x] < w) /\ (origin[i,y] >= 0 /\ origin[i,y] < h));

% non-overlap constraint
constraint diffn(origin[..,x],origin[..,y], dimension[..,x], dimension[..,y]);


% each piece must fit in the paper roll
constraint forall(i in NPIECES)
                  (((dimension[i,x] + origin[i,x]) <= w) /\ ((dimension[i,y] + origin[i,y]) <= h));


% implied cumulative constraints 
constraint cumulative(origin[..,x], dimension[..,x], dimension[..,y], h);
constraint cumulative(origin[..,y], dimension[..,y], dimension[..,x], w);


% search
ann:search_ann;
search_ann = int_search(origin, first_fail, indomain_split);
%search_ann = int_search(origin, dom_w_deg, indomain_split);
%search_ann = int_search(origin, most_constrained, indomain_split);
solve :: search_ann satisfy;


% print the solution in the required format
output [show(w) ++ " " ++ show(h) ++ "\n"];
output [show(n) ++ "\n"];

output [
  show(dimension[i,x]) ++ " " ++ show(dimension[i,y]) ++ "   " ++ show(origin[i,x]) ++ " " ++ show(origin[i,y]) ++ "\n"
  | i in NPIECES
];


