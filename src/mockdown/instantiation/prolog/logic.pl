use_module(library(csv)).

% Conventions:
% views: U, V, W, ...
% attrs: A, B, ...
% anchors: X, Y, ...

:- discontiguous attr/1, 
                 view/1,
                 parent/2,
                 anchor/2,
                 visible/2. 

attr(left).
attr(right).
attr(top).
attr(bottom).
attr(width).
attr(height).
attr(center_x).
attr(center_y).

position(left).
position(right).
position(top).
position(bottom).
position(center_x).
position(center_y).

size(width).
size(height).

horizontal(left).
horizontal(right).
horizontal(center_x).
vertical(top).
vertical(bottom).
vertical(center_y).

anchor(V, A) :- view(V), attr(A).

sibling(V, W) :- 
    view(V),
    view(W),
    V \= W, 
    parent(U, V), 
    parent(U, W).

visible_sym(X, Y) :- 
    X = anchor(_, _),
    Y = anchor(_, _),
    visible(X, Y); visible(Y, X).

% Are views V and W horizontally visible?
visible_horizontal(V, W) :-
    view(V),
    view(W),
    V \= W,
    position(A), horizontal(A),
    position(B), horizontal(B),
    A \= B,
    visible_sym(anchor(V, A), anchor(W, B)).

% Are views V and W vertically visible?
visible_vertical(V, W) :-
    view(V),
    view(W),
    V \= W,
    position(A), vertical(A),
    position(B), vertical(B),
    A \= B,
    visible_sym(anchor(V, A), anchor(W, B)).

alignable(X, Y) :-
    X = anchor(V, A), 
    Y = anchor(W, B), 
    anchor(V, A), 
    anchor(W, B), 
    V \= W, 
    visible_horizontal(V, W), 
    position(A), vertical(A),
    position(B), vertical(B),
    A = B.

alignable(X, Y) :-
    X = anchor(V, A),
    Y = anchor(W, B),
    anchor(V, A), 
    anchor(W, B),
    V \= W,
    visible_vertical(V, W),
    position(A), horizontal(A),
    position(B), horizontal(B),
    A = B.

alignable_sym(X, Y) :-
    X = anchor(_, _),
    Y = anchor(_, _),
    alignable(X, Y); alignable(Y, X).

% --------------------
% | Constraint Forms |
% --------------------

spacing(V, A, W, B) :-
    spacing_sib(V, A, W, B);
    spacing_pc(V, A, W, B).

% Spacing between siblings.
spacing_sib(V, A, W, B) :-
    sibling(V, W),
    visible_sym(anchor(V, A), anchor(W, B)),
    ((A == right, B == left);(A == bottom, B == top)).

% Spacing between parent (V) and child (W).
spacing_pc(V, A, W, B) :-
    parent(V, W),
    visible_sym(anchor(V, A), anchor(W, B)),
    A = B.

alignment(V, A, W, B) :-
    X = anchor(V, A),
    Y = anchor(W, B),
    alignable(X, Y).

absolute_size(V, A) :-
    anchor(V, A),
    size(A).

parent_relative_size(V, A, W, B) :-
    anchor(V, A),
    anchor(W, B),
    parent(V, W),
    size(A),
    size(B),
    A == B.

aspect_ratio_size(V) :-
    anchor(V, width),  % redundant?
    anchor(V, height).

% List constraints of type F.
lscons(F, FileName) :-
    findall(constraint(F, V, A, W, B), call(F, V, A, W, B), Constraints),
    write(Constraints),
    csv_write_file(FileName, Constraints).

% 0. How to load stuff in Prolog.
% 1. Series of commands to type in to output a CSV of spacing.
% 2. How to write a new constraint.
% 3. Very very basic prolog tutorial for 2.
%     - "e.g. , = and, ; = or"