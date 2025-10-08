# Mork Chainer Installation Guide

## PeTTa Installation

### Step 1: Clone the PeTTa Repository
Clone the PeTTa repository from GitHub:

```bash
git clone https://github.com/patham9/PeTTa
```

### Step 2: Set Up with `uv`
1. Update the `pyproject.toml` file to point to the cloned PeTTa repository:

   ```toml
   [tool.uv.sources]
   petta = { path = "../PeTTa", editable = true }
   ```

2. Sync the dependencies using `uv`:

   ```bash
   uv sync
   ```

### Alternative: Install with `pip`
Alternatively, you can install PeTTa in editable mode using `pip`:

```bash
pip install -e path/to/PeTTa
```

## Mork Installation
To install Mork, follow the instructions in the [Mork repository](https://github.com/trueagi-io/MORK/tree/main).
