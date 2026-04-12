#!/usr/bin/env python3
"""Validate Learning/task_metadata.json.

Checks:
- top-level schema and task field types
- unique task IDs
- referenced task files exist in the repo
- prerequisite IDs refer to existing tasks
- prerequisite graph has no cycles
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_METADATA_PATH = REPO_ROOT / "Learning" / "task_metadata.json"


REQUIRED_FIELDS: dict[str, type | tuple[type, ...]] = {
    "id": str,
    "file": str,
    "tier": str,
    "hint": str,
    "prerequisites": list,
    "difficulty": (int, float),
    "expected_minutes": (int, float),
    "downstream_relevance": (int, float),
    "concepts": list,
}


def _is_non_bool_number(value: Any) -> bool:
    return isinstance(value, (int, float)) and not isinstance(value, bool)


def _validate_task_schema(index: int, task: Any, errors: list[str]) -> None:
    label = f"tasks[{index}]"
    if not isinstance(task, dict):
        errors.append(f"{label}: expected object, got {type(task).__name__}")
        return

    missing = [field for field in REQUIRED_FIELDS if field not in task]
    for field in missing:
        errors.append(f"{label}: missing required field '{field}'")

    for field, expected_type in REQUIRED_FIELDS.items():
        if field not in task:
            continue
        value = task[field]
        if not isinstance(value, expected_type):
            expected_name = (
                ", ".join(t.__name__ for t in expected_type)
                if isinstance(expected_type, tuple)
                else expected_type.__name__
            )
            errors.append(
                f"{label}.{field}: expected {expected_name}, got {type(value).__name__}"
            )

    if "id" in task and isinstance(task["id"], str) and not task["id"].strip():
        errors.append(f"{label}.id: must be a non-empty string")

    if "file" in task and isinstance(task["file"], str) and not task["file"].strip():
        errors.append(f"{label}.file: must be a non-empty string")

    if "prerequisites" in task and isinstance(task["prerequisites"], list):
        for i, prereq in enumerate(task["prerequisites"]):
            if not isinstance(prereq, str) or not prereq.strip():
                errors.append(f"{label}.prerequisites[{i}]: expected non-empty string")

    if "concepts" in task and isinstance(task["concepts"], list):
        for i, concept in enumerate(task["concepts"]):
            if not isinstance(concept, str) or not concept.strip():
                errors.append(f"{label}.concepts[{i}]: expected non-empty string")

    for numeric_field, min_value in [
        ("difficulty", 1),
        ("expected_minutes", 0),
        ("downstream_relevance", 0),
    ]:
        if numeric_field in task:
            value = task[numeric_field]
            if not _is_non_bool_number(value):
                errors.append(f"{label}.{numeric_field}: expected number")
            elif value < min_value:
                errors.append(f"{label}.{numeric_field}: must be >= {min_value}")


def _detect_cycle(graph: dict[str, list[str]]) -> list[str] | None:
    VISITING = 1
    DONE = 2
    state: dict[str, int] = {}
    stack: list[str] = []

    def dfs(node: str) -> list[str] | None:
        state[node] = VISITING
        stack.append(node)

        for neighbor in graph.get(node, []):
            neighbor_state = state.get(neighbor, 0)
            if neighbor_state == 0:
                cycle = dfs(neighbor)
                if cycle:
                    return cycle
            elif neighbor_state == VISITING:
                start = stack.index(neighbor)
                return stack[start:] + [neighbor]

        stack.pop()
        state[node] = DONE
        return None

    for node in graph:
        if state.get(node, 0) == 0:
            cycle = dfs(node)
            if cycle:
                return cycle

    return None


def validate_metadata(path: Path) -> list[str]:
    errors: list[str] = []

    if not path.is_file():
        return [f"metadata file not found: {path}"]

    try:
        raw = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        return [f"invalid JSON in {path}: {exc}"]

    if not isinstance(raw, dict):
        return ["top-level JSON value must be an object"]

    tasks = raw.get("tasks")
    if not isinstance(tasks, list):
        return ["top-level key 'tasks' must be a list"]

    for i, task in enumerate(tasks):
        _validate_task_schema(i, task, errors)

    valid_tasks = [t for t in tasks if isinstance(t, dict) and isinstance(t.get("id"), str)]

    id_to_task: dict[str, dict[str, Any]] = {}
    for task in valid_tasks:
        tid = task["id"]
        if tid in id_to_task:
            errors.append(f"duplicate task id: {tid}")
        else:
            id_to_task[tid] = task

    known_ids = set(id_to_task)

    for tid, task in id_to_task.items():
        file_value = task.get("file")
        if isinstance(file_value, str) and file_value.strip():
            rel_path = Path(file_value)
            full_path = (REPO_ROOT / rel_path).resolve()
            try:
                full_path.relative_to(REPO_ROOT)
            except ValueError:
                errors.append(f"{tid}: file path escapes repo root: {file_value}")
                continue
            if not full_path.is_file():
                errors.append(f"{tid}: file path does not exist: {file_value}")

        prereqs = task.get("prerequisites")
        if isinstance(prereqs, list):
            for prereq in prereqs:
                if not isinstance(prereq, str):
                    continue
                if prereq == tid:
                    errors.append(f"{tid}: cannot depend on itself")
                elif prereq not in known_ids:
                    errors.append(f"{tid}: prerequisite does not exist: {prereq}")

    graph = {
        tid: [pr for pr in (task.get("prerequisites") or []) if isinstance(pr, str) and pr in known_ids]
        for tid, task in id_to_task.items()
    }
    cycle = _detect_cycle(graph)
    if cycle:
        errors.append("cycle detected in prerequisites: " + " -> ".join(cycle))

    return errors


def main() -> None:
    parser = argparse.ArgumentParser(description="Validate task metadata integrity")
    parser.add_argument(
        "--metadata",
        type=Path,
        default=DEFAULT_METADATA_PATH,
        help="Path to task metadata JSON (default: Learning/task_metadata.json)",
    )
    args = parser.parse_args()

    errors = validate_metadata(args.metadata)
    if errors:
        print("Task metadata validation failed:")
        for error in errors:
            print(f"- {error}")
        raise SystemExit(1)

    print(f"Task metadata is valid: {args.metadata}")


if __name__ == "__main__":
    main()
