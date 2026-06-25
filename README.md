# QC Checking Inventor App (PDF Drawing Checker)

A Python Tkinter application designed to load fabrication drawing PDFs, read BOM (Bill of Materials) and table entries, and verify that each item has a matching callout and matching dimensions/length elsewhere in the drawing. The application flags items as `PASS` or `FAIL` and provides spelling checks on drawing text to improve quality control before fabrication.

---

## Features

- **Automated BOM Parsing**: Extracts BOM tables (columns like POS, Description, Length, Thickness, and Qty) directly from PDF text.
- **Callout Verification**: Scans drawing pages to verify that every item listed in the BOM has a corresponding visual callout/label.
- **Length & Dimension Auditing**: Cross-checks the length/dimensions listed in the BOM against callouts and other dimensions found on drawing pages.
- **OCR Fallback**: Integrates Tesseract OCR and Poppler utilities to convert PDF pages into images and run OCR when standard text extraction is unavailable.
- **Interactive GUI**: Fully-featured Tkinter GUI showing PASS/FAIL status per item, detailed error highlights, spell checking tab, and check history.
- **Unit Testing**: Modular core engine (`qc_logic.py`) decoupled from the GUI layer to enable automated testing.

---

## Installation & Setup

### 1. Python Dependencies

Install the required python packages:
```bash
pip install PyPDF2 pdfplumber pdf2image pytesseract pillow pyspellchecker
```

### 2. System Requirements (for OCR Fallback)

If checking scanned drawings (non-vector PDFs) which require OCR, install the following:
- **Tesseract OCR**: Install [Tesseract](https://github.com/tesseract-ocr/tesseract) and ensure it is added to your system's `PATH`.
- **Poppler Utilities**: Required by `pdf2image`. On Windows, download Poppler, extract it, and add the `bin` folder to your system's `PATH` or locate the path when prompted by the application.

---

## How to Run

Launch the desktop application by running:
```bash
python app.py
```

---

## Running Tests

Run the test suite to verify the core checking algorithms:
```bash
python -m unittest test_qc_logic.py
```

---

## Development Workflow & Contribution Guidelines

To maintain high project quality and collaborate effectively like a real product team, please use the following workflow:

### 1. Open Issues for Planning
Before writing any code or making changes, create a new issue on GitHub to document what you plan to do (e.g., "Write unit tests for row parser", "Add health check endpoint").

### 2. Create a Feature Branch
Do not commit directly to the `main` branch. Create a descriptively named branch for your issue:
```bash
# Get the latest changes from main
git checkout main
git pull origin main

# Create and switch to your feature branch
git checkout -b feature/your-feature-name
```

### 3. Implement Changes & Add Tests
Write your code, make sure the formatting is clean, and add corresponding tests in `test_qc_logic.py`. Ensure all unit tests pass before committing.

### 4. Push Branch & Create a Pull Request
Push your branch to GitHub and open a Pull Request (PR) to merge into `main`:
```bash
git add .
git commit -m "feat: implement your feature description (resolves #<issue_number>)"
git push origin feature/your-feature-name
```
Navigate to your repository page on GitHub and click **Compare & pull request**. Mention the issue number in the PR description (e.g., `Closes #12`) so GitHub closes the issue automatically when the PR is merged.