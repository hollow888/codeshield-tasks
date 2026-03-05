

from __future__ import annotations

import ast
import csv
import os
import tkinter as tk
from dataclasses import dataclass
from tkinter import filedialog, messagebox
from tkinter import ttk
from typing import Dict, List, Set, Tuple




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
        # Simple statements
        simple = (
            ast.Assign, ast.AnnAssign, ast.AugAssign, ast.Expr, ast.Pass, ast.Return,
            ast.Raise, ast.Import, ast.ImportFrom, ast.Assert
        )
        if isinstance(st, simple):
            n = cfg.new_node(type(st).__name__)
            for inc in incoming:
                cfg.add_edge(inc, n)
            if isinstance(st, (ast.Return, ast.Raise)):
                return {n}, set()  # terminal
            return {n}, {n}

        # If / elif / else
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

        # Loops
        if isinstance(st, (ast.For, ast.While)):
            loop_cond = cfg.new_node(type(st).__name__ + "Cond")
            for inc in incoming:
                cfg.add_edge(inc, loop_cond)

            _, body_end = self._build_block(cfg, st.body, incoming={loop_cond})
            if not st.body:
                body_end = {loop_cond}

            # back edge(s)
            for ep in body_end:
                cfg.add_edge(ep, loop_cond)

            # fall-through
            merge = cfg.new_node(type(st).__name__ + "Merge")
            cfg.add_edge(loop_cond, merge)
            return {loop_cond}, {merge}

        # Try/Except (coarse)
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

        # Fallback unknown statement
        n = cfg.new_node("Stmt:" + type(st).__name__)
        for inc in incoming:
            cfg.add_edge(inc, n)
        return {n}, {n}


@dataclass
class FunctionResult:
    file: str
    function: str
    complexity: int
    E: int
    N: int
    P: int
    extras: int


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


def analyze_python_source(source: str, filename: str) -> List[FunctionResult]:
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
            out.append(FunctionResult(
                file=filename,
                function=node.name,
                complexity=cc,
                E=cfg.E,
                N=cfg.N,
                P=P,
                extras=extras
            ))
    return out


def iter_py_files(path: str) -> List[str]:
    if os.path.isfile(path):
        return [path] if path.endswith(".py") else []
    found: List[str] = []
    for root, _, files in os.walk(path):
        for f in files:
            if f.endswith(".py"):
                found.append(os.path.join(root, f))
    return sorted(found)


# ---------------------------
# Tkinter UI
# ---------------------------

class CodeShieldApp(tk.Tk):
    def __init__(self) -> None:
        super().__init__()
        self.title("CodeShield")
        self.geometry("980x560")
        self.minsize(900, 520)

        self.selected_path = tk.StringVar(value="")
        self.status = tk.StringVar(value="Ready.")
        self.results: List[FunctionResult] = []

        self._build_ui()

    def _build_ui(self) -> None:
        top = ttk.Frame(self, padding=12)
        top.pack(fill="x")

        ttk.Label(top, text="Artefact path (file or folder):").grid(row=0, column=0, sticky="w")
        entry = ttk.Entry(top, textvariable=self.selected_path)
        entry.grid(row=1, column=0, columnspan=4, sticky="ew", pady=(4, 8))

        btn_file = ttk.Button(top, text="Choose File", command=self.choose_file)
        btn_dir = ttk.Button(top, text="Choose Folder", command=self.choose_folder)
        btn_scan = ttk.Button(top, text="Run Scan", command=self.run_scan)
        btn_export = ttk.Button(top, text="Export CSV", command=self.export_csv)

        btn_file.grid(row=2, column=0, sticky="w")
        btn_dir.grid(row=2, column=1, sticky="w", padx=(8, 0))
        btn_scan.grid(row=2, column=2, sticky="w", padx=(16, 0))
        btn_export.grid(row=2, column=3, sticky="w", padx=(8, 0))

        top.columnconfigure(0, weight=1)
        top.columnconfigure(1, weight=0)
        top.columnconfigure(2, weight=0)
        top.columnconfigure(3, weight=0)

        # Table
        mid = ttk.Frame(self, padding=(12, 0, 12, 12))
        mid.pack(fill="both", expand=True)

        cols = ("file", "function", "cc", "E", "N", "P", "extras")
        self.tree = ttk.Treeview(mid, columns=cols, show="headings")
        self.tree.heading("file", text="File")
        self.tree.heading("function", text="Function")
        self.tree.heading("cc", text="Complexity (CC)")
        self.tree.heading("E", text="E")
        self.tree.heading("N", text="N")
        self.tree.heading("P", text="P")
        self.tree.heading("extras", text="Extras (boolops)")

        self.tree.column("file", width=340, anchor="w")
        self.tree.column("function", width=170, anchor="w")
        self.tree.column("cc", width=120, anchor="center")
        self.tree.column("E", width=70, anchor="center")
        self.tree.column("N", width=70, anchor="center")
        self.tree.column("P", width=70, anchor="center")
        self.tree.column("extras", width=120, anchor="center")

        vsb = ttk.Scrollbar(mid, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=vsb.set)

        self.tree.pack(side="left", fill="both", expand=True)
        vsb.pack(side="right", fill="y")

        # Bottom summary
        bottom = ttk.Frame(self, padding=12)
        bottom.pack(fill="x")

        self.summary_label = ttk.Label(bottom, text="No results yet.")
        self.summary_label.pack(side="left")

        ttk.Label(bottom, textvariable=self.status).pack(side="right")

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

    def run_scan(self) -> None:
        path = self.selected_path.get().strip()
        if not path:
            messagebox.showwarning("CodeShield", "Please choose a file or folder first.")
            return
        if not os.path.exists(path):
            messagebox.showerror("CodeShield", "Selected path does not exist.")
            return

        self.status.set("Scanning...")
        self.update_idletasks()

        files = iter_py_files(path)
        if not files:
            self.status.set("Ready.")
            messagebox.showinfo("CodeShield", "No .py files found to analyse.")
            return

        # Clear table
        for item in self.tree.get_children():
            self.tree.delete(item)
        self.results.clear()

        total_cc = 0
        fn_count = 0
        file_count = 0

        try:
            for fp in files:
                with open(fp, "r", encoding="utf-8") as f:
                    src = f.read()

                rel = os.path.relpath(fp, start=os.path.dirname(path) if os.path.isfile(path) else path)
                funcs = analyze_python_source(src, filename=rel)
                if funcs:
                    file_count += 1
                for r in funcs:
                    self.results.append(r)
                    total_cc += r.complexity
                    fn_count += 1
                    self.tree.insert("", "end", values=(
                        r.file, r.function, r.complexity, r.E, r.N, r.P, r.extras
                    ))

            if fn_count == 0:
                self.summary_label.config(text="No top-level functions found.")
            else:
                avg = total_cc / fn_count
                self.summary_label.config(
                    text=f"Files analysed: {file_count} | Functions: {fn_count} | Total CC: {total_cc} | Avg CC: {avg:.2f}"
                )

            self.status.set("Done.")
        except SyntaxError as e:
            self.status.set("Ready.")
            messagebox.showerror("Parse error", f"SyntaxError while parsing:\n{e}")
        except OSError as e:
            self.status.set("Ready.")
            messagebox.showerror("File error", f"Failed reading files:\n{e}")

    def export_csv(self) -> None:
        if not self.results:
            messagebox.showinfo("CodeShield", "No results to export. Run a scan first.")
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
                w.writerow(["file", "function", "complexity", "E", "N", "P", "extras"])
                for r in self.results:
                    w.writerow([r.file, r.function, r.complexity, r.E, r.N, r.P, r.extras])
            messagebox.showinfo("CodeShield", f"Exported results to:\n{fp}")
        except OSError as e:
            messagebox.showerror("Export error", f"Could not write CSV:\n{e}")


def main() -> None:
    app = CodeShieldApp()
    app.mainloop()


if __name__ == "__main__":
    main()