--------------------- MODULE TransactionHistoryIterator ---------------------

EXTENDS Naturals, Sequences, TLC

(*
--algorithm TransactionHistoryIterator {
variables mainOplog = <<>>;

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
                \o <<[ts |-> frame[Len(frame)].ts,
                      op |-> "importOplog",
                      ns |-> tree]>>;
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
    \*either {
        \* Add regular "insert" oplog entry (op="i") to the stack.
        localStack := localStack \o <<<<[ts |-> ts, op |-> "i"]>>>>;

    ts := ts - 1;
    
    goto loop;
}
  
{ 
    main:
    call makeOplog(5);
    madeOplog:
    print(mainOplog);
}
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "cf02536e" /\ chksum(tla) = "4c5ed73f")
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
                                \o <<[ts |-> frame[Len(frame)].ts,
                                      op |-> "importOplog",
                                      ns |-> tree]>>
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
        /\ localStack' = localStack \o <<<<[ts |-> ts, op |-> "i"]>>>>
        /\ ts' = ts - 1
        /\ pc' = "loop"
        /\ UNCHANGED << mainOplog, stack, maxTS, state, frame, leaf, tree >>

makeOplog == loop \/ pop \/ importOplog \/ appendEntries \/ done \/ push

main == /\ pc = "main"
        /\ /\ maxTS' = 5
           /\ stack' = << [ procedure |->  "makeOplog",
                            pc        |->  "madeOplog",
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

madeOplog == /\ pc = "madeOplog"
             /\ PrintT((mainOplog))
             /\ pc' = "Done"
             /\ UNCHANGED << mainOplog, stack, maxTS, localStack, state, ts, 
                             frame, leaf, tree >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == makeOplog \/ main \/ madeOplog
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Fri Sep 17 16:41:19 EDT 2021 by emptysquare
\* Created Thu Sep 16 13:06:35 EDT 2021 by emptysquare
