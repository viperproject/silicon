#!/bin/bash

# find_files() {
#   local name_pattern=$1
#   local message="------- Finding files matching '${name_pattern}' -------"

#   echo ${message}

#   # Regarding find>
#   #   * -path <path> -prune prevents find from recursing into <path>
#   #   * -o denotes logical OR
#   #   * -iname "*" could be replaced by, e.g. "*.scala"
#   #   * -type f must come right before -exec (no idea, why)
#   # Regarding grep:
#   #   * -I ignores binary files
#   #   * -U prevents removing line endings (crucial on Windows)
#   #   * -l means grep will print matching files, not matches themselves

#   find . \
#     -path ./.\* -prune -o \
#     -path ./target -prune -o \
#     -path ./tmp -prune -o \
#     -path ./common/target -prune -o \
#     -path ./project/project -prune -o \
#     -path ./project/target -prune -o \
#     -iname "${name_pattern}" \
#     -type f \
#     -exec grep -IUl $'\r' {} \;  
# }

# find_files_with_gitgrep <message> <pathspecs...>
# where
#   <message> is a string
#   <pathspecs> are git-grep compatible path specifications
# 
# Uses git-grep to search file linefeeds (\r) in all git versioned files that match <pathspecs>.
# Outputs
#   1. <message>
#   2. all found files, one filename per line
#   3. total file count
find_files_with_gitgrep() {
  local message="$1"
  local pathspecs="${@:2}"

  echo "============ ${message}"

  git \
    grep -Il $'\r' -- ${pathspecs} \
    | tee /dev/tty \
    | wc -l \
    | xargs echo "---- Matching file count: "
}

# A list of git-grep compatible pathspecs, one per invocation of find_files_with_gitgrep
declare -a pathspecs_groups=("*.scala" "*.vpr *.sil" "*.bat")

# Invoke find_files_with_gitgrep for each pathspecs group
for pathspecs in "${pathspecs_groups[@]}"; do
  find_files_with_gitgrep "Searching in files matching ${pathspecs}" "${pathspecs}"
done

# Invoke find_files_with_gitgrep such that it searches all files not searched previously.
# This is achieved by first flattening the pathspec groups and negating each pathspec,
# and finally invoking find_files_with_gitgrep with the list of negated pathspecs as argument.
read -r -a pathspecs <<< "${pathspecs_groups[@]}" # Flatten pathspecs_groups (split by IFS=" ")
for i in "${!pathspecs[@]}"; do
  pathspecs[$i]=":!${pathspecs[$i]}" # git-grep syntax for negated pathspecs
done
find_files_with_gitgrep "Searching in all remaining files" "${pathspecs[@]}"

# Hints:
# * Copy printed filenames into a file "crlf.txt", then run "cat crlf.txt | xargs -n1 dos2unix"
#   to convert each file's line endings using "dos2unix"
