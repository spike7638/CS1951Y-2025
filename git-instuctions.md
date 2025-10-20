# Git Workflow for Isabelle

##  Start of Class

### Switch to `main` and update

```bash
git checkout main
git pull origin main
```

### Create a new branch for your proof

```bash
git checkout -b chapter-1-2-ap3
```

This creates a new branch from `main` and switches to it.

## During Class

While making edits in Isabelle, save the buffer and commit your work.

```bash
git add chapter-1-2.thy
git commit -m "Draft Chapter 1.2 proof (AP3)"
```

## At the End of Class

### Push your branch to GitHub

```bash
git push -u origin chapter-1-2-ap3
```

The `-u` flag tells Git to remember the branch, so next time you can just run:

```bash
git push
```

### Create a Pull Request (PR) on GitHub

1. Go the repo's [GitHub page](https://github.com/spike7638/CS1951Y-2025)
2. Switch to your branch button on the left side.
![Switch-Branch](Switch-Branch.png)
3. Click `Contribute` and you should have an option to `Open pull request`
![Contribute](Contribute.png)

#### Alt steps:

This is an alternate way of doing this the official way

1. Go the repo's [GitHub page](https://github.com/spike7638/CS1951Y-2025)
2. Then go to the [Pull Requests](https://github.com/spike7638/CS1951Y-2025/pulls) tab at the top
3. Then create [New pull Request](https://github.com/spike7638/CS1951Y-2025/compare) and the branch you want to merge should be listed at the bottom
4. Ideally it'll say `Able to merge` and you can click `Create pull request`


At the end of the day, you or Robert can review and merge PRs into `main`.

---

# Troubleshooting

### "Your branch is behind 'origin/main'"

Run:

```bash
git fetch origin
git merge origin/main
```

Or if you haven't committed anything yet:

```bash
git reset --hard origin/main
```
This will reset your branch to match `main`, so be careful if you have uncommitted changes.

### "Updates were rejected because the remote contains work you do not have locally"

That means someone else pushed to `main` while you were working.

Run:

```bash
git checkout main
git pull origin main
git checkout chapter-1-2-ap3
git rebase main
```

Now the commit on `main` is added before your commits so you may have to check if anything broke.

Then push again:

```bash
git push
```

### Merge conflicts during `pull` or `rebase`

Let's work on this together on VSCode

