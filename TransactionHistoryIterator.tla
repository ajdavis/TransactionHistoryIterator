--------------------- MODULE TransactionHistoryIterator ---------------------

EXTENDS Naturals, Sequences, TLC

Range(n, m) == [i \in 1..(m-n+1) |-> i+n-1]

SubSequences(s) == 
  (*************************************************************************)
  (* Sequences in the same order as the sequence s, with zero or some      *)
  (* elements omitted.                                                     *)
  (*************************************************************************)
    LET n == Len(s)
        masks == [1..n -> BOOLEAN]
        F[i \in 0..n, mask \in masks] == 
          IF i = 0 THEN <<>>
                   ELSE IF mask[i] THEN Append(F[i-1, mask], s[i])
                                   ELSE F[i-1, mask]
     IN {result \in {F[n, m]: m \in masks}: result # <<>>}

OplogEntry(ts) == [ts |-> ts]
ImportOplogEntry(ts, oplog) == [ts |-> ts, importedOplog |-> oplog]

Pow(mant, exp) ==
    LET F[n \in 0..exp] == IF n <= 1 THEN mant ELSE mant * F[n-1]
     IN F[exp]


(*
h       c       c + 2^(h-1)
5       1       17
4       17      25
3       25      29
2       29      31
1       31      32
*)

Oplogs(n) ==
  (*************************************************************************)
  (* A set of trees of oplogs, each has max depth n.                       *)
  (* Make all grids of height n, width 2^n, with values in {TRUE, FALSE,   *)
  (* importOplog}. Make a tree from each grid, starting at the top where height h=n. The oplog entry at h  *)
  (* is a regular entry, or absent, or an importOplog entry depending on   *)
  (* the value at grid row h. Set the current grid column c to 1 for the tree root, and at  *)
  (* each branch the imported      *)
  (* oplog uses column c + 2^(h-1). *) 
  (*************************************************************************)
  LET width == Pow(2, n)
      grids == [{<<x,y>>: x \in 1..n, y \in 1..width} -> {"entry", "omit", "importOplog"}]
      F[c \in 1..width, h \in 0..n, grid \in grids] == 
        IF h = 0
        THEN <<>>
        ELSE
            CASE
                grid[c, h] = "entry" ->
                    <<h>> \o F[c, h-1, grid]
                    []
                grid[c, h] = "omit" ->
                    <<>> \o F[c, h-1, grid]
                    []
                grid[c, h] = "importOplog" ->
                    <<>> \o F[c, h-1, grid]
   IN {F[1, n, g]: g \in grids}


(* --algorithm TransactionHistoryIterator {
{
print(Range(0, 5));
print(Range(1, 4));
print(Range(10, 12));
print(SubSequences(Range(1, 3)));
print(SubSequences(Range(10, 13)));
print(Pow(2, 3));
print(Pow(0, 0));
print(Pow(3, 2));
print(Pow(5, 1));
print(Oplogs(1));
print(Oplogs(2));
print(Oplogs(3)); \* Error: Attempted to construct a set with too many elements (>1000000)
} } *)
\* BEGIN TRANSLATION (chksum(pcal) = "c8a606d5" /\ chksum(tla) = "b8296715")
VARIABLE pc

vars == << pc >>

Init == /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ PrintT((Range(0, 5)))
         /\ PrintT((Range(1, 4)))
         /\ PrintT((Range(10, 12)))
         /\ PrintT((SubSequences(Range(1, 3))))
         /\ PrintT((SubSequences(Range(10, 13))))
         /\ PrintT((Pow(2, 3)))
         /\ PrintT((Pow(0, 0)))
         /\ PrintT((Pow(3, 2)))
         /\ PrintT((Pow(5, 1)))
         /\ PrintT((Oplogs(1)))
         /\ PrintT((Oplogs(2)))
         /\ PrintT((Oplogs(3)))
         /\ pc' = "Done"

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Fri Sep 17 10:44:59 EDT 2021 by emptysquare
\* Created Thu Sep 16 13:06:35 EDT 2021 by emptysquare
