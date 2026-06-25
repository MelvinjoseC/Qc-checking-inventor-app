name: Bug Report
description: File a bug report to help us improve the app
labels: [bug]
body:
  - type: markdown
    attributes:
      value: |
        Thank you for reporting this issue! Please provide as much detail as possible to help us reproduce and fix it.
  - type: textarea
    id: description
    attributes:
      label: Description
      description: A clear and concise description of what the bug is.
      placeholder: Describe what went wrong...
    validations:
      required: true
  - type: textarea
    id: steps-to-reproduce
    attributes:
      label: Steps to Reproduce
      description: Explain how we can reproduce the behavior.
      placeholder: |
        1. Open the PDF QC App
        2. Upload drawing file XYZ.pdf
        3. Observe crash/error...
    validations:
      required: true
  - type: textarea
    id: expected-behavior
    attributes:
      label: Expected Behavior
      description: What did you expect to happen?
      placeholder: The row should pass check...
    validations:
      required: true
  - type: textarea
    id: environment
    attributes:
      label: Environment Info
      description: Python version, dependencies, OS, etc.
      placeholder: |
        - OS: Windows 11
        - Python: 3.10
        - PyPDF2: 3.0.1
        - pdfplumber: 0.10.2
    validations:
      required: false
