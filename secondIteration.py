#!/usr/bin/env python3
"""
CodeShield – Technical Debt & Security Scanner (Prototype UI)

Features:
- Scan a Python file or folder
- Cyclomatic Complexity per function (simplified CFG): M = E - N + 2P (+ boolean-op extras)
- Security red flags (regex rules + one AST heuristic)
- LOC counting (effective LOC: non-empty, non-comment)
- Vulnerability Density: red_flags / LOC * 1000
- Technical Debt Index (TDI): wC*Complexity + wV*VulnDensity
- Risk classification with configurable threshold
- CSV/JSON export
- Editable security ruleset (regex)

Assumptions:
- Python-only prototype
- CFG is intraprocedural per function (P = 1 in this construction)
- Some rules are heuristic and may produce false positives/negatives
"""

from __future__ import annotations

import ast
import csv
import json
import os
import re
import tkinter as tk
from dataclasses import dataclass, asdict
from datetime import datetime
from tkinter import filedialog, messagebox
from tkinter import ttk
from typing import Dict, List, Set, Tuple


# ---------------------------
# Security rules
# ---------------------------

@dataclass
class RedFlagRule:
    id: str
    name: str
    severity: str  # Low/Med/High
    pattern: str   # regex
    description: str


DEFAULT_RULES: List[RedFlagRule] = [
    RedFlagRule(
        id="RF001",
        name="Hardcoded secret (password/api key/token)",
        severity="High",
        pattern=r"(?i)\b(password|passwd|pwd|api[_-]?key|secret|token)\b\s*=\s*['\"][^'\"]+['\"]",
        description="Detects assignment of credential-like values to string literals."
    ),
    RedFlagRule(
        id="RF002",
        name="SQL concatenation (possible injection)",
        severity="High",
        pattern=r"(?i)\b(SELECT|INSERT|UPDATE|DELETE)\b.+['\"].*['\"]\s*\+\s*\w+",
        description="Detects SQL string concatenation with a variable."
    ),
    RedFlagRule(
        id="RF003",
        name="Weak crypto/hash function (MD5/SHA1)",
        severity="Med",
        pattern=r"(?i)\b(md5|sha1)\s*\(",
        description="Detects use of weak/deprecated hashing algorithms."
    ),
    RedFlagRule(
        id="RF004",
        name="Insecure debug configuration",
        severity="Med",
        pattern=r"(?i)\bdebug\s*=\s*True\b",
        description="Detects debug enabled in configuration."
    ),
    RedFlagRule(
        id="RF005",
        name="Direct input() usage (may require validation)",
        severity="Low",
        pattern=r"(?i)\binput\s*\(",
        description="Flags direct input() usage (validation/sanitisation may be needed)."
    ),
    RedFlagRule(
        id="RF006",
        name="Hardcoded privileged role check (e.g., admin)",
        severity="Med",
        pattern=r"(?i)\b(user_role|role)\b\s*==\s*['\"]admin['\"]",
        description="Hardcoded privileged role string; may bypass authz framework or lack validation."
    ),
    RedFlagRule(
        id="RF007",
        name="Business logic thresholds hardcoded in code",
        severity="Low",
        pattern=r"(?i)\b(bonus|salary|threshold|limit|years_employed|account_balance|balance)\b\s*(>=|>|<=|<)\s*\d+",
        description="Heuristic: rules/thresholds embedded in code. Better externalise to configuration/policy."
    ),
    RedFlagRule(
        id="RF009",
        name="Unsafe shell execution (os.system / subprocess shell=True)",
        severity="High",
        pattern=r"(?i)\b(os\.system|popen)\s*\(|subprocess\.\w+\s*\(.*shell\s*=\s*True",
        description="Potential command injection if arguments are influenced by user input."
    ),
    RedFlagRule(
        id="RF010",
        name="Unsafe deserialisation (pickle.loads / yaml.load)",
        severity="High",
        pattern=r"(?i)\bpickle\.loads\s*\(|yaml\.load\s*\(",
        description="Potential arbitrary code execution via unsafe deserialisation."
    ),
    RedFlagRule(
        id="RF011",
        name="Insecure random for secrets (random.*)",
        severity="Med",
        pattern=r"(?i)\brandom\.(random|randint|choice)\s*\(",
        description="random module is not suitable for secrets; use secrets module."
    ),
]


# ---------------------------
# CFG / complexity
# ---------------------------

@dataclass(frozen=True)
class Node:
    id: int
    label: str


class CFG:
    def __init__(self) -> None:
        self._next_id = 1
        self.nodes: Dict[int, Node] = {}
        self.edges: Set[Tuple[int, int]] = set()
        self.entry = self.new_node("ENTRY")
        self.exit = self.new_node("EXIT")

    def new_node(self, label: str) -> int:
        nid = self._next_id
        self._next_id += 1
        self.nodes[nid] = Node(nid, label)
        return nid

    def add_edge(self, a: int, b: int) -> None:
        self.edges.add((a, b))

    @property
    def N(self) -> int:
        return len(self.nodes)

    @property
    def E(self) -> int:
        return len(self.edges)


def cyclomatic_complexity(E: int, N: int, P: int = 1) -> int:
    return E - N + 2 * P


def count_boolops(expr: ast.AST) -> int:
    extra = 0
    for node in ast.walk(expr):
        if isinstance(node, ast.BoolOp):
            extra += max(0, len(node.values) - 1)
    return extra


class CFGBuilder:
    def build_for_function(self, fn: ast.FunctionDef | ast.AsyncFunctionDef) -> CFG:
        cfg = CFG()
        _, end_points = self._build_block(cfg, fn.body, incoming={cfg.entry})
        if not end_points:
            cfg.add_edge(cfg.entry, cfg.exit)
        else:
            for ep in end_points:
                cfg.add_edge(ep, cfg.exit)
        return cfg

    def _build_block(self, cfg: CFG, stmts: List[ast.stmt], incoming: Set[int]) -> Tuple[Set[int], Set[int]]:
        if not stmts:
            return set(), set(incoming)

        start_nodes: Set[int] = set()
        current_incoming = set(incoming)

        for i, st in enumerate(stmts):
            st_start, st_end = self._build_stmt(cfg, st, current_incoming)
            if i == 0:
                start_nodes |= st_start
            current_incoming = st_end

        return start_nodes, current_incoming

    def _build_stmt(self, cfg: CFG, st: ast.stmt, incoming: Set[int]) -> Tuple[Set[int], Set[int]]:
        simple = (
            ast.Assign, ast.AnnAssign, ast.AugAssign, ast.Expr, ast.Pass, ast.Return,
            ast.Raise, ast.Import, ast.ImportFrom, ast.Assert
        )
        if isinstance(st, simple):
            n = cfg.new_node(type(st).__name__)
            for inc in incoming:
                cfg.add_edge(inc, n)
            if isinstance(st, (ast.Return, ast.Raise)):
                return {n}, set()
            return {n}, {n}

        if isinstance(st, ast.If):
            cond = cfg.new_node("IfCond")
            for inc in incoming:
                cfg.add_edge(inc, cond)

            _, then_end = self._build_block(cfg, st.body, incoming={cond})
            if not st.body:
                then_end = {cond}

            _, else_end = self._build_block(cfg, st.orelse, incoming={cond})
            if not st.orelse:
                else_end = {cond}

            merge = cfg.new_node("IfMerge")
            for ep in (then_end | else_end):
                cfg.add_edge(ep, merge)
            return {cond}, {merge}

        if isinstance(st, (ast.For, ast.While)):
            loop_cond = cfg.new_node(type(st).__name__ + "Cond")
            for inc in incoming:
                cfg.add_edge(inc, loop_cond)

            _, body_end = self._build_block(cfg, st.body, incoming={loop_cond})
            if not st.body:
                body_end = {loop_cond}

            for ep in body_end:
                cfg.add_edge(ep, loop_cond)

            merge = cfg.new_node(type(st).__name__ + "Merge")
            cfg.add_edge(loop_cond, merge)
            return {loop_cond}, {merge}

        if isinstance(st, ast.Try):
            t = cfg.new_node("Try")
            for inc in incoming:
                cfg.add_edge(inc, t)

            _, body_end = self._build_block(cfg, st.body, incoming={t})
            if not st.body:
                body_end = {t}

            handler_ends: Set[int] = set()
            for h in st.handlers:
                hnode = cfg.new_node("Except")
                cfg.add_edge(t, hnode)
                _, he = self._build_block(cfg, h.body, incoming={hnode})
                handler_ends |= (he if he else {hnode})

            merge = cfg.new_node("TryMerge")
            for ep in (body_end | handler_ends):
                cfg.add_edge(ep, merge)

            if st.finalbody:
                _, fend = self._build_block(cfg, st.finalbody, incoming={merge})
                return {t}, (fend if fend else {merge})

            return {t}, {merge}

        n = cfg.new_node("Stmt:" + type(st).__name__)
        for inc in incoming:
            cfg.add_edge(inc, n)
        return {n}, {n}


# ---------------------------
# Findings + aggregation
# ---------------------------

@dataclass
class Finding:
    rule_id: str
    rule_name: str
    severity: str
    line: int
    snippet: str


@dataclass
class FunctionResult:
    file: str
    function: str
    complexity: int
    E: int
    N: int
    P: int
    extras: int


@dataclass
class FileResult:
    file: str
    loc: int
    red_flags: int
    vuln_density: float
    complexity_sum: int
    tdi: float
    risk: str
    flagged: bool
    findings: List[Finding]
    functions: List[FunctionResult]


def iter_py_files(path: str) -> List[str]:
    if os.path.isfile(path):
        return [path] if path.endswith(".py") else []
    found: List[str] = []
    for root, _, files in os.walk(path):
        for f in files:
            if f.endswith(".py"):
                found.append(os.path.join(root, f))
    return sorted(found)


def count_loc(source: str) -> int:
    loc = 0
    for line in source.splitlines():
        s = line.strip()
        if not s:
            continue
        if s.startswith("#"):
            continue
        loc += 1
    return loc


def scan_red_flags_regex(source: str, rules: List[RedFlagRule]) -> List[Finding]:
    findings: List[Finding] = []
    lines = source.splitlines()

    compiled: List[Tuple[RedFlagRule, re.Pattern]] = []
    for r in rules:
        try:
            compiled.append((r, re.compile(r.pattern)))
        except re.error:
            continue

    for i, line in enumerate(lines, start=1):
        for r, rx in compiled:
            if rx.search(line):
                snippet = line.strip()
                if len(snippet) > 160:
                    snippet = snippet[:157] + "..."
                findings.append(Finding(r.id, r.name, r.severity, i, snippet))
    return findings


class InputValidationHeuristic(ast.NodeVisitor):
    """
    Heuristic:
    - Collect variables assigned from input()
    - Mark as validated if wrapped in int()/float() at assignment or later conversion
    - If an unvalidated input var is used in comparison or arithmetic, emit a finding
    """
    def __init__(self, source_lines: List[str]) -> None:
        self.source_lines = source_lines
        self.input_vars: Set[str] = set()
        self.validated_vars: Set[str] = set()
        self.findings: List[Finding] = []

    def visit_Assign(self, node: ast.Assign) -> None:
        targets = [t.id for t in node.targets if isinstance(t, ast.Name)]

        if self._is_input_call(node.value):
            for n in targets:
                self.input_vars.add(n)

        if self._is_numeric_conversion_of_input(node.value):
            for n in targets:
                self.input_vars.add(n)
                self.validated_vars.add(n)

        self.generic_visit(node)

    def visit_Call(self, node: ast.Call) -> None:
        if isinstance(node.func, ast.Name) and node.func.id in ("int", "float") and node.args:
            if isinstance(node.args[0], ast.Name):
                self.validated_vars.add(node.args[0].id)
        self.generic_visit(node)

    def visit_Compare(self, node: ast.Compare) -> None:
        for n in self._names_in_expr(node):
            if n in self.input_vars and n not in self.validated_vars:
                self._add(node.lineno)
        self.generic_visit(node)

    def visit_BinOp(self, node: ast.BinOp) -> None:
        for n in self._names_in_expr(node):
            if n in self.input_vars and n not in self.validated_vars:
                self._add(node.lineno)
        self.generic_visit(node)

    def _add(self, lineno: int) -> None:
        line = self.source_lines[lineno - 1].strip() if 1 <= lineno <= len(self.source_lines) else ""
        if len(line) > 160:
            line = line[:157] + "..."
        self.findings.append(Finding(
            rule_id="RF008",
            rule_name="Missing input validation (heuristic)",
            severity="Med",
            line=lineno,
            snippet=line or "Unvalidated input used in comparison/arithmetic."
        ))

    @staticmethod
    def _is_input_call(node: ast.AST) -> bool:
        return isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "input"

    @staticmethod
    def _is_numeric_conversion_of_input(node: ast.AST) -> bool:
        if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id in ("int", "float")):
            return False
        return bool(node.args) and InputValidationHeuristic._is_input_call(node.args[0])

    @staticmethod
    def _names_in_expr(node: ast.AST) -> Set[str]:
        names: Set[str] = set()
        for sub in ast.walk(node):
            if isinstance(sub, ast.Name):
                names.add(sub.id)
        return names


def scan_red_flags_ast(source: str) -> List[Finding]:
    try:
        tree = ast.parse(source)
    except SyntaxError:
        return []
    visitor = InputValidationHeuristic(source.splitlines())
    visitor.visit(tree)
    return visitor.findings


def compute_extras(fn: ast.FunctionDef | ast.AsyncFunctionDef) -> int:
    extra = 0
    for node in ast.walk(fn):
        if isinstance(node, ast.If):
            extra += count_boolops(node.test)
        elif isinstance(node, ast.While):
            extra += count_boolops(node.test)
        elif isinstance(node, ast.IfExp):
            extra += 1 + count_boolops(node.test)
    return extra


def analyze_functions(source: str, filename: str) -> List[FunctionResult]:
    tree = ast.parse(source)
    builder = CFGBuilder()
    out: List[FunctionResult] = []

    for node in tree.body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            cfg = builder.build_for_function(node)
            P = 1
            base = cyclomatic_complexity(cfg.E, cfg.N, P)
            extras = compute_extras(node)
            cc = base + extras
            out.append(FunctionResult(filename, node.name, cc, cfg.E, cfg.N, P, extras))

    return out


def compute_vuln_density(red_flags: int, loc: int) -> float:
    return 0.0 if loc <= 0 else (red_flags / loc) * 1000.0


def compute_tdi(complexity_score: int, vuln_density: float, w_c: float, w_v: float) -> float:
    return (complexity_score * w_c) + (vuln_density * w_v)


def classify_risk(tdi: float, threshold: float) -> Tuple[str, bool]:
    if tdi >= threshold:
        return "HIGH", True
    if tdi >= threshold * 0.6:
        return "MEDIUM", False
    return "LOW", False


# ---------------------------
# UI
# ---------------------------

class CodeShieldApp(tk.Tk):
    def __init__(self) -> None:
        super().__init__()
        self.title("CodeShield")
        self.geometry("1150x680")
        self.minsize(980, 600)

        self.selected_path = tk.StringVar(value="")
        self.status = tk.StringVar(value="Ready.")

        self.threshold = tk.DoubleVar(value=50.0)
        self.weight_complexity = tk.DoubleVar(value=0.5)
        self.weight_vuln = tk.DoubleVar(value=0.5)

        self.rules: List[RedFlagRule] = list(DEFAULT_RULES)
        self.file_results: List[FileResult] = []

        self._build_ui()

    def _build_ui(self) -> None:
        self._build_top()
        self._build_tabs()
        self._build_bottom()

    def _build_top(self) -> None:
        top = ttk.Frame(self, padding=12)
        top.pack(fill="x")

        ttk.Label(top, text="Artefact path (file or folder):").grid(row=0, column=0, sticky="w")
        ttk.Entry(top, textvariable=self.selected_path).grid(row=1, column=0, columnspan=6, sticky="ew", pady=(4, 10))

        ttk.Button(top, text="Choose File", command=self.choose_file).grid(row=2, column=0, sticky="w")
        ttk.Button(top, text="Choose Folder", command=self.choose_folder).grid(row=2, column=1, sticky="w", padx=(8, 0))
        ttk.Button(top, text="Run Scan", command=self.run_scan).grid(row=2, column=2, sticky="w", padx=(16, 0))
        ttk.Button(top, text="Rules", command=self.open_rules_editor).grid(row=2, column=3, sticky="w", padx=(8, 0))
        ttk.Button(top, text="Export CSV", command=self.export_csv).grid(row=2, column=4, sticky="w", padx=(16, 0))
        ttk.Button(top, text="Export JSON", command=self.export_json).grid(row=2, column=5, sticky="w", padx=(8, 0))

        cfg = ttk.LabelFrame(top, text="TDI Configuration", padding=10)
        cfg.grid(row=3, column=0, columnspan=6, sticky="ew", pady=(12, 0))

        ttk.Label(cfg, text="Threshold (TDI):").grid(row=0, column=0, sticky="w")
        ttk.Entry(cfg, textvariable=self.threshold, width=10).grid(row=0, column=1, sticky="w", padx=(6, 18))

        ttk.Label(cfg, text="Weight Complexity:").grid(row=0, column=2, sticky="w")
        ttk.Entry(cfg, textvariable=self.weight_complexity, width=6).grid(row=0, column=3, sticky="w", padx=(6, 18))

        ttk.Label(cfg, text="Weight Vuln Density:").grid(row=0, column=4, sticky="w")
        ttk.Entry(cfg, textvariable=self.weight_vuln, width=6).grid(row=0, column=5, sticky="w", padx=(6, 0))

        ttk.Label(cfg, text="(Recommended: weights sum to 1.0)").grid(row=0, column=6, sticky="w", padx=(18, 0))

        top.columnconfigure(0, weight=1)

    def _build_tabs(self) -> None:
        mid = ttk.Frame(self, padding=(12, 0, 12, 12))
        mid.pack(fill="both", expand=True)

        self.nb = ttk.Notebook(mid)
        self.nb.pack(fill="both", expand=True)

        self.tab_dash = ttk.Frame(self.nb, padding=10)
        self.nb.add(self.tab_dash, text="Dashboard")
        self._build_dashboard_tab()

        self.tab_funcs = ttk.Frame(self.nb, padding=10)
        self.nb.add(self.tab_funcs, text="Functions")
        self._build_functions_tab()

        self.tab_findings = ttk.Frame(self.nb, padding=10)
        self.nb.add(self.tab_findings, text="Security Findings")
        self._build_findings_tab()

    def _build_dashboard_tab(self) -> None:
        self.dash_summary = ttk.Label(self.tab_dash, text="No scan yet.")
        self.dash_summary.pack(anchor="w", pady=(0, 10))

        cols = ("file", "loc", "complexity", "redflags", "vulnd", "tdi", "risk", "flagged")
        self.dash_tree = ttk.Treeview(self.tab_dash, columns=cols, show="headings", height=16)
        headings = {
            "file": "File",
            "loc": "LOC",
            "complexity": "Complexity (sum)",
            "redflags": "Red Flags",
            "vulnd": "Vuln Density",
            "tdi": "TDI",
            "risk": "Risk",
            "flagged": "Alert"
        }
        for c in cols:
            self.dash_tree.heading(c, text=headings[c])

        self.dash_tree.column("file", width=380, anchor="w")
        self.dash_tree.column("loc", width=70, anchor="center")
        self.dash_tree.column("complexity", width=140, anchor="center")
        self.dash_tree.column("redflags", width=90, anchor="center")
        self.dash_tree.column("vulnd", width=110, anchor="center")
        self.dash_tree.column("tdi", width=90, anchor="center")
        self.dash_tree.column("risk", width=80, anchor="center")
        self.dash_tree.column("flagged", width=70, anchor="center")

        vsb = ttk.Scrollbar(self.tab_dash, orient="vertical", command=self.dash_tree.yview)
        self.dash_tree.configure(yscrollcommand=vsb.set)

        self.dash_tree.pack(side="left", fill="both", expand=True)
        vsb.pack(side="right", fill="y")

    def _build_functions_tab(self) -> None:
        cols = ("file", "function", "cc", "E", "N", "P", "extras")
        self.func_tree = ttk.Treeview(self.tab_funcs, columns=cols, show="headings", height=18)
        for c, t in [
            ("file", "File"),
            ("function", "Function"),
            ("cc", "Cyclomatic Complexity"),
            ("E", "E"),
            ("N", "N"),
            ("P", "P"),
            ("extras", "Extras (boolops)")
        ]:
            self.func_tree.heading(c, text=t)

        self.func_tree.column("file", width=380, anchor="w")
        self.func_tree.column("function", width=220, anchor="w")
        self.func_tree.column("cc", width=180, anchor="center")
        self.func_tree.column("E", width=70, anchor="center")
        self.func_tree.column("N", width=70, anchor="center")
        self.func_tree.column("P", width=70, anchor="center")
        self.func_tree.column("extras", width=140, anchor="center")

        vsb = ttk.Scrollbar(self.tab_funcs, orient="vertical", command=self.func_tree.yview)
        self.func_tree.configure(yscrollcommand=vsb.set)
        self.func_tree.pack(side="left", fill="both", expand=True)
        vsb.pack(side="right", fill="y")

    def _build_findings_tab(self) -> None:
        cols = ("file", "rule", "severity", "line", "snippet")
        self.find_tree = ttk.Treeview(self.tab_findings, columns=cols, show="headings", height=18)
        for c, t in [
            ("file", "File"),
            ("rule", "Rule"),
            ("severity", "Severity"),
            ("line", "Line"),
            ("snippet", "Snippet")
        ]:
            self.find_tree.heading(c, text=t)

        self.find_tree.column("file", width=280, anchor="w")
        self.find_tree.column("rule", width=340, anchor="w")
        self.find_tree.column("severity", width=90, anchor="center")
        self.find_tree.column("line", width=70, anchor="center")
        self.find_tree.column("snippet", width=360, anchor="w")

        vsb = ttk.Scrollbar(self.tab_findings, orient="vertical", command=self.find_tree.yview)
        self.find_tree.configure(yscrollcommand=vsb.set)
        self.find_tree.pack(side="left", fill="both", expand=True)
        vsb.pack(side="right", fill="y")

    def _build_bottom(self) -> None:
        bottom = ttk.Frame(self, padding=12)
        bottom.pack(fill="x")
        ttk.Label(bottom, textvariable=self.status).pack(side="right")
        ttk.Label(bottom, text="Scan Python code for complexity and security risk.").pack(side="left")

    # ---------------------------
    # Actions
    # ---------------------------

    def choose_file(self) -> None:
        fp = filedialog.askopenfilename(
            title="Select a Python file",
            filetypes=[("Python files", "*.py"), ("All files", "*.*")]
        )
        if fp:
            self.selected_path.set(fp)

    def choose_folder(self) -> None:
        d = filedialog.askdirectory(title="Select a folder containing .py files")
        if d:
            self.selected_path.set(d)

    def open_rules_editor(self) -> None:
        win = tk.Toplevel(self)
        win.title("Security Rules")
        win.geometry("960x540")

        cols = ("id", "name", "severity", "pattern")
        tree = ttk.Treeview(win, columns=cols, show="headings", height=12)
        for c, t in [("id", "ID"), ("name", "Name"), ("severity", "Severity"), ("pattern", "Regex Pattern")]:
            tree.heading(c, text=t)
        tree.column("id", width=80, anchor="center")
        tree.column("name", width=320, anchor="w")
        tree.column("severity", width=90, anchor="center")
        tree.column("pattern", width=440, anchor="w")
        tree.pack(fill="x", padx=12, pady=(12, 8))

        for r in self.rules:
            tree.insert("", "end", values=(r.id, r.name, r.severity, r.pattern))

        form = ttk.LabelFrame(win, text="Selected Rule", padding=10)
        form.pack(fill="both", expand=True, padx=12, pady=(0, 12))

        rid = tk.StringVar()
        rname = tk.StringVar()
        rsev = tk.StringVar(value="Low")
        rpat = tk.StringVar()

        desc = tk.Text(form, height=6, wrap="word")

        def set_desc(text: str):
            desc.delete("1.0", "end")
            desc.insert("1.0", text)

        def on_select(_evt=None):
            sel = tree.selection()
            if not sel:
                return
            values = tree.item(sel[0], "values")
            rule = next((x for x in self.rules if x.id == values[0]), None)
            if not rule:
                return
            rid.set(rule.id)
            rname.set(rule.name)
            rsev.set(rule.severity)
            rpat.set(rule.pattern)
            set_desc(rule.description)

        tree.bind("<<TreeviewSelect>>", on_select)

        ttk.Label(form, text="ID").grid(row=0, column=0, sticky="w")
        ttk.Entry(form, textvariable=rid, width=12).grid(row=0, column=1, sticky="w", padx=(6, 18))
        ttk.Label(form, text="Severity").grid(row=0, column=2, sticky="w")
        ttk.Combobox(form, textvariable=rsev, values=["Low", "Med", "High"], width=10, state="readonly")\
            .grid(row=0, column=3, sticky="w", padx=(6, 0))

        ttk.Label(form, text="Name").grid(row=1, column=0, sticky="w", pady=(10, 0))
        ttk.Entry(form, textvariable=rname, width=80).grid(row=1, column=1, columnspan=3, sticky="ew", pady=(10, 0), padx=(6, 0))

        ttk.Label(form, text="Regex Pattern").grid(row=2, column=0, sticky="w", pady=(10, 0))
        ttk.Entry(form, textvariable=rpat, width=80).grid(row=2, column=1, columnspan=3, sticky="ew", pady=(10, 0), padx=(6, 0))

        ttk.Label(form, text="Description").grid(row=3, column=0, sticky="nw", pady=(10, 0))
        desc.grid(row=3, column=1, columnspan=3, sticky="nsew", pady=(10, 0), padx=(6, 0))

        def refresh_table():
            for item in tree.get_children():
                tree.delete(item)
            for rr in self.rules:
                tree.insert("", "end", values=(rr.id, rr.name, rr.severity, rr.pattern))

        def save_update():
            if not rid.get().strip():
                messagebox.showwarning("Rules", "Rule ID is required.")
                return
            try:
                re.compile(rpat.get())
            except re.error as e:
                messagebox.showerror("Rules", f"Invalid regex:\n{e}")
                return

            description = desc.get("1.0", "end").strip()
            existing = next((x for x in self.rules if x.id == rid.get().strip()), None)

            if existing is None:
                self.rules.append(RedFlagRule(
                    id=rid.get().strip(),
                    name=rname.get().strip(),
                    severity=rsev.get().strip() or "Low",
                    pattern=rpat.get(),
                    description=description
                ))
            else:
                existing.name = rname.get().strip()
                existing.severity = rsev.get().strip() or "Low"
                existing.pattern = rpat.get()
                existing.description = description

            refresh_table()
            messagebox.showinfo("Rules", "Rule saved/updated.")

        def delete_rule():
            sel = tree.selection()
            if not sel:
                return
            values = tree.item(sel[0], "values")
            rid_local = values[0]
            self.rules = [x for x in self.rules if x.id != rid_local]
            refresh_table()
            rid.set(""); rname.set(""); rsev.set("Low"); rpat.set(""); set_desc("")
            messagebox.showinfo("Rules", "Rule deleted.")

        btns = ttk.Frame(form)
        btns.grid(row=4, column=1, columnspan=3, sticky="e", pady=(12, 0))
        ttk.Button(btns, text="Save/Update", command=save_update).pack(side="left", padx=8)
        ttk.Button(btns, text="Delete", command=delete_rule).pack(side="left")

        form.columnconfigure(1, weight=1)
        form.rowconfigure(3, weight=1)

    def run_scan(self) -> None:
        path = self.selected_path.get().strip()
        if not path:
            messagebox.showwarning("CodeShield", "Choose a file or folder first.")
            return
        if not os.path.exists(path):
            messagebox.showerror("CodeShield", "Selected path does not exist.")
            return

        w_c = float(self.weight_complexity.get())
        w_v = float(self.weight_vuln.get())
        if w_c < 0 or w_v < 0:
            messagebox.showerror("Configuration", "Weights must be non-negative.")
            return
        if abs((w_c + w_v) - 1.0) > 0.01:
            if not messagebox.askyesno("Configuration", "Weights do not sum to 1.0. Continue anyway?"):
                return

        threshold = float(self.threshold.get())

        self.status.set("Scanning...")
        self.update_idletasks()

        for t in (self.dash_tree, self.func_tree, self.find_tree):
            for item in t.get_children():
                t.delete(item)
        self.file_results.clear()

        files = iter_py_files(path)
        if not files:
            self.status.set("Ready.")
            messagebox.showinfo("CodeShield", "No .py files found.")
            return

        try:
            total_loc = 0
            total_flags = 0
            total_complexity = 0
            high_risk_count = 0

            relbase = os.path.dirname(path) if os.path.isfile(path) else path

            for fp in files:
                with open(fp, "r", encoding="utf-8") as f:
                    src = f.read()

                rel = os.path.relpath(fp, start=relbase)

                funcs = analyze_functions(src, rel)
                complexity_sum = sum(fr.complexity for fr in funcs)

                loc = count_loc(src)

                findings = scan_red_flags_regex(src, self.rules)
                findings += scan_red_flags_ast(src)

                red_flags = len(findings)
                vuln_density = compute_vuln_density(red_flags, loc)

                tdi = compute_tdi(complexity_sum, vuln_density, w_c, w_v)
                risk, flagged = classify_risk(tdi, threshold)
                if risk == "HIGH":
                    high_risk_count += 1

                fr = FileResult(
                    file=rel,
                    loc=loc,
                    red_flags=red_flags,
                    vuln_density=vuln_density,
                    complexity_sum=complexity_sum,
                    tdi=tdi,
                    risk=risk,
                    flagged=flagged,
                    findings=findings,
                    functions=funcs
                )
                self.file_results.append(fr)

                self.dash_tree.insert("", "end", values=(
                    rel, loc, complexity_sum, red_flags,
                    f"{vuln_density:.2f}", f"{tdi:.2f}", risk, "YES" if flagged else ""
                ))

                for r in funcs:
                    self.func_tree.insert("", "end", values=(
                        r.file, r.function, r.complexity, r.E, r.N, r.P, r.extras
                    ))

                for fd in findings:
                    self.find_tree.insert("", "end", values=(
                        rel, f"{fd.rule_id} {fd.rule_name}", fd.severity, fd.line, fd.snippet
                    ))

                total_loc += loc
                total_flags += red_flags
                total_complexity += complexity_sum

            avg_tdi = (sum(x.tdi for x in self.file_results) / len(self.file_results)) if self.file_results else 0.0
            self.dash_summary.config(
                text=(
                    f"Files analysed: {len(self.file_results)} | "
                    f"Total LOC: {total_loc} | Total complexity: {total_complexity} | "
                    f"Total red flags: {total_flags} | Avg TDI: {avg_tdi:.2f} | "
                    f"HIGH risk files: {high_risk_count} (threshold={threshold})"
                )
            )
            self.status.set("Done.")
        except SyntaxError as e:
            self.status.set("Ready.")
            messagebox.showerror("Parse error", f"SyntaxError while parsing:\n{e}")
        except OSError as e:
            self.status.set("Ready.")
            messagebox.showerror("File error", f"Failed reading files:\n{e}")

    def export_csv(self) -> None:
        if not self.file_results:
            messagebox.showinfo("Export", "Run a scan first.")
            return
        fp = filedialog.asksaveasfilename(
            title="Save CSV",
            defaultextension=".csv",
            filetypes=[("CSV files", "*.csv")]
        )
        if not fp:
            return

        try:
            with open(fp, "w", newline="", encoding="utf-8") as f:
                w = csv.writer(f)
                w.writerow(["file", "loc", "complexity_sum", "red_flags", "vuln_density", "tdi", "risk", "flagged"])
                for r in self.file_results:
                    w.writerow([
                        r.file, r.loc, r.complexity_sum, r.red_flags,
                        f"{r.vuln_density:.4f}", f"{r.tdi:.4f}", r.risk, r.flagged
                    ])
            messagebox.showinfo("Export", f"CSV exported:\n{fp}")
        except OSError as e:
            messagebox.showerror("Export error", f"Could not write CSV:\n{e}")

    def export_json(self) -> None:
        if not self.file_results:
            messagebox.showinfo("Export", "Run a scan first.")
            return
        fp = filedialog.asksaveasfilename(
            title="Save JSON report",
            defaultextension=".json",
            filetypes=[("JSON files", "*.json")]
        )
        if not fp:
            return

        payload = {
            "tool": "CodeShield Prototype",
            "generated_at": datetime.utcnow().isoformat() + "Z",
            "config": {
                "threshold": float(self.threshold.get()),
                "weight_complexity": float(self.weight_complexity.get()),
                "weight_vuln_density": float(self.weight_vuln.get()),
                "rules_regex": [asdict(r) for r in self.rules],
                "rules_ast": ["RF008 Missing input validation (heuristic)"],
            },
            "results": [
                {
                    "file": r.file,
                    "loc": r.loc,
                    "complexity_sum": r.complexity_sum,
                    "red_flags": r.red_flags,
                    "vuln_density": r.vuln_density,
                    "tdi": r.tdi,
                    "risk": r.risk,
                    "flagged": r.flagged,
                    "functions": [asdict(fn) for fn in r.functions],
                    "findings": [asdict(fd) for fd in r.findings],
                }
                for r in self.file_results
            ],
        }

        try:
            with open(fp, "w", encoding="utf-8") as f:
                json.dump(payload, f, indent=2)
            messagebox.showinfo("Export", f"JSON exported:\n{fp}")
        except OSError as e:
            messagebox.showerror("Export error", f"Could not write JSON:\n{e}")


def main() -> None:
    app = CodeShieldApp()
    app.mainloop()


if __name__ == "__main__":
    main()