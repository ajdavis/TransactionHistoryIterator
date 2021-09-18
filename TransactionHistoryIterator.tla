--------------------- MODULE TransactionHistoryIterator ---------------------

EXTENDS Naturals, Sequences, TLC

(*
--algorithm TransactionHistoryIterator {
(*
mainOplog is the Merge Recipient's oplog tree.
retryableWriteTimestamp is the timestamp of a regular oplog entry (not an
importOplog entry) that the TransactionHistoryIterator wants to find in
the tree.
*) 
variables mainOplog = <<>>, retryableWriteTimestamp;

(*
Make an oplog tree, e.g.:

<<
  [ts |-> 3, op |-> "importOplog", ns |->
    <<
      [ts |-> 1, op |-> "importOplog", ns |-> <<>>]
    >>
  ],
  [ts |-> 1, op |-> "i"]
>>

Each entry has a "ts" (timestamp) value. Each is a regular insert (op="i") or
an importOplog entry. If the latter, there is an "ns" field which is a list of
oplog entries, i.e. an imported oplog that branches off its parent. The tree
is ordered with the highest timestamps on top. 

It's natural to express the set of all oplog trees of height H in TLA+, but
TLC complains "Attempted to construct a set with too many elements (>1000000)."
So we have to construct one tree at a time. I've chosen to do this in PlusCal,
but PlusCal doesn't do recursive functions with return values, so I had to
write an explicit stack-based procedure.
*)

procedure makeOplog(maxTS)
    \* localStack is a list of lists of oplog entries. Each list in localStack is a
    \* "frame" of our stack, since Pluscal procedures don't do full recursion.
    variables localStack = <<>>, state = "push", ts = maxTS, frame, leaf, tree;
{
loop:
    if (ts = 0) {
        state := "pop";
    };
    
    if (state = "pop") {
        if (Len(localStack) = 1) {
            done:
            mainOplog := localStack[1];
            return;
        };

        
        pop:
        \* List of entries that we've accumulated lower down the tree.        
        tree := localStack[Len(localStack)];
        \* Pop the stack
        localStack := SubSeq(localStack, 1, Len(localStack)-1);
        \* List of entries at our current stack frame.
        frame := localStack[Len(localStack)];
        \* Final entry of current frame.
        leaf := frame[Len(frame)];
        \* The timestamp at the current level of the tree.
        ts := tree[1].ts;
        
        if (leaf.op = "importOplog" /\ leaf.ns = <<>>) {
            \* Use the entries accumulated so far as the imported oplog
            \* and start descending again.
            state := "push";
            importOplog:
            localStack :=
                SubSeq(localStack, 1, Len(localStack)-1) 
                \o <<<<[ts |-> frame[Len(frame)].ts,
                        op |-> "importOplog",
                        ns |-> tree]>>>>;
        };
        
        appendEntries:
        if (leaf.op # "importOplog" \/ leaf.ns # <<>>) {
            \* Append tree to current frame's list of entries.
            localStack :=
                SubSeq(localStack, 1, Len(localStack)-1)
                \o  
                <<frame \o tree>>;
        };
        
        goto loop;
    };
    
    push:
    either {
        \* Add regular "insert" oplog entry (op="i") to the stack.
        localStack := localStack \o <<<<[ts |-> ts, op |-> "i"]>>>>;
        either {
            \* Maybe this is the entry that TransactionHistoryIterator wants.
            retryableWriteTimestamp := ts;
        } or {
            skip;
        }
    } or {
        \* Add importOplog entry.
        localStack := localStack \o <<<<[ts |-> ts, op |-> "importOplog", ns |-> <<>>]>>>>;
    } or {
        \* No entry at this timestamp.
        skip;
    };        

    descend:
    ts := ts - 1;
    
    goto loop;
}

procedure TransactionHistoryIterator_next(nextOpTime)
    variables nextOplog = mainOplog, nextImport, nextOpTime;
{
    \* last importOplog entry with ts > _nextOpTime in _nextOplog
    nextImport := CHOOSE entry \in nextOplog: entry.ts > 
}
  
{ 
    main:
    call makeOplog(3);
    madeOplog:
    print(mainOplog);
}
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "5691a855" /\ chksum(tla) = "4167063a")
CONSTANT defaultInitValue
VARIABLES mainOplog, pc, stack, maxTS, localStack, state, ts, frame, leaf, 
          tree

vars == << mainOplog, pc, stack, maxTS, localStack, state, ts, frame, leaf, 
           tree >>

Init == (* Global variables *)
        /\ mainOplog = <<>>
        (* Procedure makeOplog *)
        /\ maxTS = defaultInitValue
        /\ localStack = <<>>
        /\ state = "push"
        /\ ts = maxTS
        /\ frame = defaultInitValue
        /\ leaf = defaultInitValue
        /\ tree = defaultInitValue
        /\ stack = << >>
        /\ pc = "main"

loop == /\ pc = "loop"
        /\ IF ts = 0
              THEN /\ state' = "pop"
              ELSE /\ TRUE
                   /\ state' = state
        /\ IF state' = "pop"
              THEN /\ IF Len(localStack) = 1
                         THEN /\ pc' = "done"
                         ELSE /\ pc' = "pop"
              ELSE /\ pc' = "push"
        /\ UNCHANGED << mainOplog, stack, maxTS, localStack, ts, frame, leaf, 
                        tree >>

pop == /\ pc = "pop"
       /\ tree' = localStack[Len(localStack)]
       /\ localStack' = SubSeq(localStack, 1, Len(localStack)-1)
       /\ frame' = localStack'[Len(localStack')]
       /\ leaf' = frame'[Len(frame')]
       /\ ts' = tree'[1].ts
       /\ IF leaf'.op = "importOplog" /\ leaf'.ns = <<>>
             THEN /\ state' = "push"
                  /\ pc' = "importOplog"
             ELSE /\ pc' = "appendEntries"
                  /\ state' = state
       /\ UNCHANGED << mainOplog, stack, maxTS >>

importOplog == /\ pc = "importOplog"
               /\ localStack' = SubSeq(localStack, 1, Len(localStack)-1)
                                \o <<<<[ts |-> frame[Len(frame)].ts,
                                        op |-> "importOplog",
                                        ns |-> tree]>>>>
               /\ pc' = "appendEntries"
               /\ UNCHANGED << mainOplog, stack, maxTS, state, ts, frame, leaf, 
                               tree >>

appendEntries == /\ pc = "appendEntries"
                 /\ IF leaf.op # "importOplog" \/ leaf.ns # <<>>
                       THEN /\ localStack' = SubSeq(localStack, 1, Len(localStack)-1)
                                             \o
                                             <<frame \o tree>>
                       ELSE /\ TRUE
                            /\ UNCHANGED localStack
                 /\ pc' = "loop"
                 /\ UNCHANGED << mainOplog, stack, maxTS, state, ts, frame, 
                                 leaf, tree >>

done == /\ pc = "done"
        /\ mainOplog' = localStack[1]
        /\ pc' = Head(stack).pc
        /\ localStack' = Head(stack).localStack
        /\ state' = Head(stack).state
        /\ ts' = Head(stack).ts
        /\ frame' = Head(stack).frame
        /\ leaf' = Head(stack).leaf
        /\ tree' = Head(stack).tree
        /\ maxTS' = Head(stack).maxTS
        /\ stack' = Tail(stack)

push == /\ pc = "push"
        /\ \/ /\ localStack' = localStack \o <<<<[ts |-> ts, op |-> "i"]>>>>
           \/ /\ localStack' = localStack \o <<<<[ts |-> ts, op |-> "importOplog", ns |-> <<>>]>>>>
           \/ /\ TRUE
              /\ UNCHANGED localStack
        /\ pc' = "descend"
        /\ UNCHANGED << mainOplog, stack, maxTS, state, ts, frame, leaf, tree >>

descend == /\ pc = "descend"
           /\ ts' = ts - 1
           /\ pc' = "loop"
           /\ UNCHANGED << mainOplog, stack, maxTS, localStack, state, frame, 
                           leaf, tree >>

makeOplog == loop \/ pop \/ importOplog \/ appendEntries \/ done \/ push
                \/ descend

main == /\ pc = "main"
        /\ /\ maxTS' = 3
           /\ stack' = << [ procedure |->  "makeOplog",
                            pc        |->  "Done",
                            localStack |->  localStack,
                            state     |->  state,
                            ts        |->  ts,
                            frame     |->  frame,
                            leaf      |->  leaf,
                            tree      |->  tree,
                            maxTS     |->  maxTS ] >>
                        \o stack
        /\ localStack' = <<>>
        /\ state' = "push"
        /\ ts' = maxTS'
        /\ frame' = defaultInitValue
        /\ leaf' = defaultInitValue
        /\ tree' = defaultInitValue
        /\ pc' = "loop"
        /\ UNCHANGED mainOplog

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == makeOplog \/ main
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Sat Sep 18 08:01:53 EDT 2021 by emptysquare
\* Created Thu Sep 16 13:06:35 EDT 2021 by emptysquare
