#!/usr/bin/env python3
"""
System Environment and Dependency Diagnostics Checker.
Validates required Python libraries and external system binaries (Poppler, Tesseract)
for CAD PDF drawing quality control.
"""

import sys
import os
import shutil
import subprocess
import importlib
from pathlib import Path
from typing import Dict, Any, Optional

import qc_logic


REQUIRED_PACKAGES = [
    "PyPDF2",
    "pdfplumber",
    "pdf2image",
    "pytesseract",
    "PIL",
]

OPTIONAL_PACKAGES = [
    "spellchecker",
]


def check_python_module(module_name: str) -> Dict[str, Any]:
    """Check if a Python package can be imported and determine its version."""
    try:
        mod = importlib.import_module(module_name)
        ver = getattr(mod, "__version__", "installed")
        return {
            "name": module_name,
            "available": True,
            "version": ver,
            "error": None
        }
    except Exception as exc:
        return {
            "name": module_name,
            "available": False,
            "version": None,
            "error": str(exc)
        }


def check_binary(
    binary_name: str,
    custom_path: Optional[str] = None,
    version_arg: str = "--version"
) -> Dict[str, Any]:
    """Check if an external system binary is found on PATH or custom path."""
    resolved_path = None
    if custom_path:
        p = Path(custom_path)
        if p.is_file():
            resolved_path = str(p)
        elif p.is_dir():
            candidate = p / (binary_name + (".exe" if sys.platform == "win32" else ""))
            if candidate.is_file():
                resolved_path = str(candidate)

    if not resolved_path:
        resolved_path = shutil.which(binary_name)

    if not resolved_path:
        return {
            "name": binary_name,
            "found": False,
            "path": None,
            "version": None
        }

    version_str = "found"
    try:
        res = subprocess.run(
            [resolved_path, version_arg],
            capture_output=True,
            text=True,
            timeout=3
        )
        if res.returncode == 0:
            version_str = res.stdout.splitlines()[0] if res.stdout else "available"
    except Exception:
        pass

    return {
        "name": binary_name,
        "found": True,
        "path": resolved_path,
        "version": version_str
    }


def run_system_diagnostics(config_path: str = "config.json") -> Dict[str, Any]:
    """
    Run full system diagnostics and return structured report.
    """
    cfg = qc_logic.load_config(config_path)

    modules_status = {}
    for pkg in REQUIRED_PACKAGES + OPTIONAL_PACKAGES:
        modules_status[pkg] = check_python_module(pkg)

    tess_path = cfg.get("tesseract_path") or None
    pop_path = cfg.get("poppler_path") or None

    tesseract_info = check_binary("tesseract", custom_path=tess_path)
    poppler_info = check_binary("pdftoppm", custom_path=pop_path, version_arg="-v")

    all_required_modules_ok = all(
        modules_status[pkg]["available"] for pkg in REQUIRED_PACKAGES
    )
    ocr_ready = tesseract_info["found"] and poppler_info["found"]

    return {
        "python_version": sys.version.split()[0],
        "platform": sys.platform,
        "required_modules": {pkg: modules_status[pkg] for pkg in REQUIRED_PACKAGES},
        "optional_modules": {pkg: modules_status[pkg] for pkg in OPTIONAL_PACKAGES},
        "binaries": {
            "tesseract": tesseract_info,
            "poppler_pdftoppm": poppler_info
        },
        "all_required_ok": all_required_modules_ok,
        "ocr_ready": ocr_ready
    }


def format_diagnostics_report(diag: Dict[str, Any]) -> str:
    """Format diagnostics dictionary into human-readable text."""
    lines = [
        "==================================================",
        "  PDF DRAWING CHECKER SYSTEM DIAGNOSTICS",
        "==================================================",
        f"Python Version: {diag['python_version']}",
        f"Platform:       {diag['platform']}",
        "",
        "--- Python Dependencies ---",
    ]

    for name, info in diag["required_modules"].items():
        status = f"[OK] Available ({info['version']})" if info["available"] else f"[MISSING] ({info['error']})"
        lines.append(f"  {name:15}: {status}")

    for name, info in diag["optional_modules"].items():
        status = f"[OK] Available ({info['version']})" if info["available"] else "[WARN] Missing (optional)"
        lines.append(f"  {name:15}: {status}")

    lines.extend([
        "",
        "--- External OCR Binaries ---",
    ])

    tess = diag["binaries"]["tesseract"]
    tess_status = f"[OK] Found at {tess['path']}" if tess["found"] else "[MISSING] Not found (OCR disabled)"
    lines.append(f"  Tesseract OCR  : {tess_status}")

    pop = diag["binaries"]["poppler_pdftoppm"]
    pop_status = f"[OK] Found at {pop['path']}" if pop["found"] else "[MISSING] Not found (pdf2image fallback disabled)"
    lines.append(f"  Poppler util   : {pop_status}")

    lines.extend([
        "",
        "--- Overall Status ---",
        f"  Core Table Extraction Engine: {'[READY]' if diag['all_required_ok'] else '[MISSING DEPENDENCIES]'}",
        f"  OCR Fallback Engine          : {'[READY]' if diag['ocr_ready'] else '[DISABLED] (Scanned PDFs only)'}",
        "==================================================",
    ])

    return "\n".join(lines)



def main() -> int:
    report = run_system_diagnostics()
    print(format_diagnostics_report(report))
    return 0 if report["all_required_ok"] else 1


if __name__ == "__main__":
    sys.exit(main())
