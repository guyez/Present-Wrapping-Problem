% pwp general case

% import for global constraints
include "globals.mzn";

% paper roll dimensions
int: h;
int: w;

% number of necessary pieces of paper to cut off
int: n;
set of int: NPIECES = 1..n;

% number of shapes that we can use (considering the rotation)
int: m;
set of int: NPIECESWR = 1..m;

% all the elements needed for the geost_bb constraint
array[int] of set of NPIECESWR: shape;
array[NPIECES] of set of int: shapeind;
array[NPIECESWR, 1..2] of int: rect_dimension;
array[NPIECESWR, 1..2] of int: rect_offset;


array[NPIECES] of var int: rotation;
array[NPIECES,1..2] of var int: origin;

% numper of different pieces of paper
int: c;
set of int: NDIFFPIECES = 1..c;

% number of copy for each piece of paper
array[NDIFFPIECES] of int: ncopy;

% useful constants 
int: x = 1;
int: y = 2;

% constraints (set the domain of the matrix origin)

constraint forall(i in NPIECES)(origin[i,x] >= 0 /\ origin[i,x] < w);
constraint forall(i in NPIECES)(origin[i,y] >= 0 /\ origin[i,y] < h);


                  
% implied cumulative constraints
constraint (cumulative([origin[i,x] | i in NPIECES ], [rect_dimension[rotation[i],x] | i in NPIECES ], [rect_dimension[rotation[i],y] | i in NPIECES ],h));
constraint (cumulative([origin[i,y] | i in NPIECES ], [rect_dimension[rotation[i],y] | i in NPIECES ], [rect_dimension[rotation[i],x] | i in NPIECES ],w));
                  
                  
% non-overlap constraint
constraint forall(i in NPIECES)(rotation[i] in shapeind[i]);
constraint geost_bb(2,rect_dimension,rect_offset,shape,origin,rotation,[0,0],[w,h]);


% find the starting index of each size
array[NDIFFPIECES] of int: base = 
  [if i = 1 then 0 else
    sum(j in 1..i-1)(ncopy[j]) endif
  | i in NDIFFPIECES];
  
% order pieces of the same size
constraint forall(i in NDIFFPIECES)(
  forall(j in 1..ncopy[i]-1)(
    lex_greater(origin[base[i]+j,..],origin[base[i]+j+1,..])));


% search
ann:search_ann;
search_ann = int_search(rotation, anti_first_fail, indomain_max);
solve :: search_ann satisfy;


% Variable selection

% anti_first_fail
% dom_w_deg
% first_fail
% input_order
% largest 
% max_regret 
% most_constrained
% occurrence
% smallest



% print the solution in the required format
output [show(w) ++ " " ++ show(h) ++ "\n"];
output [show(n) ++ "\n"];

output [
  show(rect_dimension[rotation[i],x]) ++ " " ++ show(rect_dimension[rotation[i],y]) ++ "   " ++ show(origin[i,x]) ++ " " ++ show(origin[i,y]) ++ "\n"
  | i in NPIECES
];

%output [show(rotation) ++ "\n"];
