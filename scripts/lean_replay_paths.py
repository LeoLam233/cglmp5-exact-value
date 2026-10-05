"""Contain generated caches and require self-contained production Lean sources."""
from pathlib import Path
import os


def validate_checkout_paths(root):
    root = Path(root).resolve()
    lean = root / 'lean'
    for relative in ('lean', 'lean/CGLMP5', 'lean/.lake', 'lean/.lake/build', 'lean/.lake/packages'):
        path = root / relative
        if path.is_symlink():
            raise RuntimeError('Replay refuses a symlinked source/cache directory: ' + relative)
        if not path.resolve().is_relative_to(root):
            raise RuntimeError('Replay path escapes the candidate: ' + relative)
    if not lean.is_dir() or not (lean / 'CGLMP5').is_dir():
        raise RuntimeError('Missing production Lean source directories')
    files = [lean / 'CGLMP5.lean']
    for base, directories, names in os.walk(lean / 'CGLMP5', followlinks=False):
        for name in directories:
            path = Path(base) / name
            if path.is_symlink():
                raise RuntimeError('Replay refuses a symlinked production source directory: ' + str(path))
        files.extend(Path(base) / name for name in names if name.endswith('.lean'))
    for path in files:
        if path.is_symlink() or not path.is_file() or not path.resolve().is_relative_to(lean):
            raise RuntimeError('Production Lean source is absent, linked, or outside the candidate: ' + str(path))
    packages = lean / '.lake/packages'
    if packages.exists():
        for package in packages.iterdir():
            if package.is_symlink() or not package.resolve().is_relative_to(packages):
                raise RuntimeError('Dependency checkout is linked or outside its pinned package directory: ' + str(package))
    return {'candidate_root': str(root), 'production_lean_files': len(files),
            'cache_is_internal': True, 'production_source_symlinks': False}
