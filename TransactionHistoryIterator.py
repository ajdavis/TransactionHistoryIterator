import pprint
import random
from dataclasses import dataclass
from typing import Optional


@dataclass
class OplogEntry:
    ts: int
    op: str
    ns: Optional[list["OplogEntry"]] = None


def make_oplog_recursive(ts: int):
    if ts == 0:
        return []

    entry_type = random.choice(["entry", "omit", "importOplog"])
    if entry_type == "entry":
        return [OplogEntry(ts, "i")] + make_oplog_recursive(ts - 1)
    elif entry_type == "omit":
        return [] + make_oplog_recursive(ts - 1)
    else:
        return ([OplogEntry(ts, "importOplog", make_oplog_recursive(ts - 1))]
                + make_oplog_recursive(ts - 1))


@dataclass
class Frame:
    tree: list[OplogEntry]


stack: list[Frame] = []


def make_oplog_procedural(maxTS: int):
    ts: int = maxTS
    state: str = "push"

    while True:
        if ts == 0:
            state = "pop"

        if state == "pop":
            if len(stack) == 1:
                return

            frame = stack.pop(len(stack) - 1)
            ts = frame.tree[0].ts
            leaf = stack[-1].tree[-1]
            if leaf.op == "importOplog" and not leaf.ns:
                # Use the entries accumulated so far as the imported oplog,
                # and start descending again.
                leaf.ns = frame.tree
                state = "push"
            else:
                stack[-1].tree.extend(frame.tree)

            continue

        # State is "push".
        entry_type = random.choice(["entry", "omit", "importOplog"])
        if entry_type != "omit":
            stack.append(Frame([OplogEntry(ts, entry_type)]))

        ts -= 1


def pprint_tree(tree: list[OplogEntry], indent: str = ''):
    if not tree:
        return

    print(f'{indent}{tree[0].ts}: {tree[0].op}')
    if tree[0].op == "importOplog":
        pprint_tree(tree[0].ns, indent + '  ')

    pprint_tree(tree[1:], indent)


pprint.pprint(make_oplog_recursive(5))

make_oplog_procedural(5)
pprint_tree(stack[0].tree)
