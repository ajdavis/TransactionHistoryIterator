import pprint
import random
from dataclasses import dataclass
from typing import Optional


@dataclass
class OplogEntry:
    ts: int
    op: str
    tenantIds: Optional[set[str]] = None
    ns: Optional[list["OplogEntry"]] = None


Tree = list[OplogEntry]

next_tenant_id = 0


def make_oplog_recursive(ts: int) -> (Tree, set[str]):
    """Return an oplog tree and its tenantIds."""
    global next_tenant_id

    if ts == 0:
        next_tenant_id += 1
        return [], set([next_tenant_id])

    children, tenant_ids = make_oplog_recursive(ts - 1)
    entry_type = random.choice(["entry", "omit", "importOplog"])
    if entry_type == "entry":
        return [OplogEntry(ts, "i")] + children, tenant_ids
    elif entry_type == "omit":
        return children, tenant_ids
    else:
        children_imported, tenants_imported = make_oplog_recursive(ts - 1)
        tree = (
            [OplogEntry(ts, "importOplog", tenants_imported, children_imported)]
            + children)

        return tree, tenant_ids.union(tenants_imported)


@dataclass
class Frame:
    """A stack frame used to transform from recursive to procedural."""
    # "Program counter".
    pc: str = "begin"
    # Parameter.
    ts: Optional[int] = None
    # Local stack-allocated variables.
    children: Optional[Tree] = None
    tenant_ids: Optional[set[int]] = None
    # tree: Optional[Tree] = None


def make_oplog_procedural(maxTs: int):
    global main_oplog

    local_next_tenant_id: int = 0
    local_stack: list[Frame] = [Frame(ts=maxTs)]
    return_value: Optional[(Tree, set[str])] = None

    while True:
        if not local_stack:
            main_oplog = return_value[0]
            return

        frame = local_stack[-1]
        if frame.pc == "begin":
            if frame.ts == 0:
                local_next_tenant_id += 1
                # Return.
                return_value = [], set([local_next_tenant_id])
                local_stack.pop()
                continue

            # Recurse with ts - 1.
            frame.pc = "return1"
            local_stack.append(Frame(ts=frame.ts - 1))
            continue

        elif frame.pc == "return1":
            frame.children, frame.tenant_ids = return_value
            entry_type = random.choice(["entry", "omit", "importOplog"])
            if entry_type == "entry":
                return_value = (
                    [OplogEntry(frame.ts, "i")] + frame.children,
                    frame.tenant_ids)
                local_stack.pop()
                continue
            elif entry_type == "omit":
                return_value = frame.children, frame.tenant_ids
                local_stack.pop()
                continue
            else:
                # An "importOplog" entry. Recurse with ts - 1.
                frame.pc = "return2"
                local_stack.append(Frame(ts=frame.ts - 1))
                continue
        elif frame.pc == "return2":
            children_imported, tenants_imported = return_value
            tree = (
                [OplogEntry(frame.ts, "importOplog", tenants_imported,
                            children_imported)]
                + frame.children)

            return_value = tree, frame.tenant_ids.union(tenants_imported)
            local_stack.pop()
            continue


def pprint_tree(tree: Tree, indent: str = ''):
    if not tree:
        return

    print(f'{indent}{tree[0].ts}: {tree[0].op}')
    if tree[0].op == "importOplog":
        pprint_tree(tree[0].ns, indent + '  ')

    pprint_tree(tree[1:], indent)


main_oplog, _ = make_oplog_recursive(5)
print("Recursive:")
pprint_tree(main_oplog)

make_oplog_procedural(5)
print("Procedural:")
pprint_tree(main_oplog)
