It seems to be bad practice to include your .vscode in a repository. However,
I like to share my settings across my own machines. I provide them as:

- settings.json-template
- tasks.json-template

A new user of vscode might want to use them by:

- ln -s settings.json-template settings.json
- ln -s tasks.json-template tasks.json

A more experienced user might want to use their own.
