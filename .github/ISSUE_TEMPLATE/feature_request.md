name: Feature Request
description: Suggest an idea or feature request for this project
labels: [enhancement]
body:
  - type: markdown
    attributes:
      value: |
        Thank you for suggesting a feature! Please provide details about what you would like to see and why.
  - type: textarea
    id: feature-description
    attributes:
      label: Describe the Feature
      description: A clear and concise description of what you want to happen.
      placeholder: I want the app to be able to...
    validations:
      required: true
  - type: textarea
    id: use-case
    attributes:
      label: Use Case / Motivation
      description: Why is this feature useful? What problem does it solve?
      placeholder: This will help us when checking drawings of type...
    validations:
      required: true
  - type: textarea
    id: alternatives
    attributes:
      label: Alternatives Considered
      description: Any alternative solutions or features you've considered.
      placeholder: We could also do it by...
    validations:
      required: false
  - type: textarea
    id: additional-context
    attributes:
      label: Additional Context
      description: Add any other context, mockup screenshots, or details here.
      placeholder: Screenshots or mockups...
    validations:
      required: false
