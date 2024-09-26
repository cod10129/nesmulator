# What's this folder about?

This folder contains `.nes` ROMs for testing `nesfile`.
To prevent any potential problems with the Git repository distributing possibly
copyrighted materials, the actual files are filtered out through `.gitignore`.

The test in `roms_do_parse.rs` iterates over all `.nes` files existing in this folder,
so this folder being empty is a perfectly valid and usual state.

(This is a hack to prevent the files on my local machine getting publicly pushed to Git.
History had to be rewritten here, as they were initially within my personal Git history
for this project.)
