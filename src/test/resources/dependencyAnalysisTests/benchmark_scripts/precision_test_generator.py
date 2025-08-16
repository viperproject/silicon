
import os

def remove_comments(lines: list[str]):
  cleansed = []
  for l in lines:
    if l.strip() and not l.strip().startswith("//"):
      cleansed.append(l)
  return cleansed

def read_snippets_file(path):
  with open(path, mode="r") as f:
    content = "".join(remove_comments(f.readlines()))
  snippets = content.split("SNIPPET")
  preamble = snippets[0]
  snippet_dict = {}
  for snippet in snippets[1:]:
    decl = snippet.split("$=$")
    name, definition = decl[0].strip(), decl[1].strip()
    snippet_dict[name] = definition
  return preamble, snippet_dict


def read_test_template(path):
  with open(path, mode="r") as f:
    content = "".join(f.readlines())
  snippets = content.split("method ")
  preamble = snippets[0]
  methods = snippets[1:]
  return preamble, methods
  
def extract_vars(line: str):
  _, _, after = line.partition("$PrecisionTest:")
  var_decls = after.strip().split(" ")
  read_write_vars = []
  read_only_vars = []
  invariant = ""
  acc_invariant = ""
  for decl in var_decls:
    tmp = decl.split("=")
    if(tmp[0] == "$READ_ONLY"):
      read_only_vars = read_only_vars + [v.replace(";", ",") for v in tmp[1].split(",")]
    elif(tmp[0] == "$READ_WRITE"):
      read_write_vars = read_write_vars + [v.replace(";", ",") for v in tmp[1].split(",")]
    elif(tmp[0] == "$INVARIANT"):
      invariant = "=".join(tmp[1:]).replace("$_$", " ")
    elif(tmp[0] == "$ACC_INVARIANT"):
      acc_invariant = "=".join(tmp[1:]).replace("$_$", " ")
  # print(f"line: {line}")
  # print(f"read only: {read_only_vars}")
  # print(f"read write: {read_write_vars}")
  # print()
  return read_only_vars + read_write_vars, read_write_vars, invariant, acc_invariant

def replace_vars(snippet: str, placeholder: str, vars: list[str]):
  idx = 0
  gen_vars = []
  while placeholder in snippet:
    if idx < len(vars):
      snippet = snippet.replace(f"{placeholder}{idx}", vars[idx])
    else:
      new_var = f"gen_{placeholder.replace("$", "")}{idx}{".f" if "FIELD" in placeholder else ""}"
      snippet = snippet.replace(f"{placeholder}{idx}", new_var)
      gen_vars.append(new_var)
    idx += 1
  return snippet, gen_vars

def generate_from_snippet(snippet: str, line: str):
  read_only_vars, read_write_vars, invariant, acc_invariant = extract_vars(line)
  # print(f"read_only_vars: {read_only_vars}")
  # print(f"read_write_vars:  {read_write_vars}")

  # replace variables, generate new ones if necessary
  snippet, gen_ro_refs = replace_vars(snippet, "$RO_REF_F_", [v.split(".")[0] for v in read_only_vars if v.endswith(".f")])
  snippet, gen_rw_refs = replace_vars(snippet, "$RW_REF_F_", [v.split(".")[0] for v in read_write_vars if v.endswith(".f")])
  snippet, gen_vars_ro_field = replace_vars(snippet, "$RO_INT_FIELD_", [v for v in read_only_vars if "." in v])
  snippet, gen_vars_rw_field = replace_vars(snippet, "$RW_INT_FIELD_", [v for v in read_write_vars if "." in v])
  snippet, gen_vars_ro_pure = replace_vars(snippet, "$RO_INT_PURE_", [v for v in read_only_vars if not "." in v])
  snippet, gen_vars_rw_pure = replace_vars(snippet, "$RW_INT_PURE_", [v for v in read_write_vars if not "." in v])
  snippet, gen_vars_ro = replace_vars(snippet, "$RO_INT_", read_only_vars)
  snippet, gen_vars_rw = replace_vars(snippet, "$RW_INT_", read_write_vars)

  snippet = "\nvar gen_dummy_int: Int\n" + snippet

  # assume non-aliasing of references
  generated_refs =   set(gen_rw_refs + gen_ro_refs + [v.split(".")[0] for v in (gen_vars_rw_field + gen_vars_ro_field) if "." in v]) 
  existing_refs = set([v.split(".")[0] for v in (read_write_vars+read_only_vars) if "." in v])
  # snippet = f"\n//generated: {generated_refs}\n//existing: {existing_refs}\n" + snippet
  snippet = "\n".join([f"inhale {a} != {b}" for a in generated_refs for b in existing_refs if a != b]) + snippet

  gen_vars_ro_field = gen_vars_ro_field + [f"{v}.f" for v in gen_ro_refs]
  gen_vars_rw_field = gen_vars_rw_field + [f"{v}.f" for v in gen_rw_refs]

  snippet = snippet.replace("$INVARIANT", invariant if invariant != "" else "true")
  gen_acc_invariants = [f"acc({v}, 1/2)" for v in gen_vars_ro_field] + [f"acc({v})" for v in gen_vars_rw_field]
  gen_acc_invariant = " && ".join([f"@irrelevant(\"LoopInvariant\")({v})" for v in gen_acc_invariants])
  snippet = snippet.replace("$ACC_INVARIANT", acc_invariant if acc_invariant != "" else "true")
  snippet = snippet.replace("$GEN_ACC_INVARIANT", gen_acc_invariant if gen_acc_invariant != "" else "true")

  # declare and initialize newly generated vars
  snippet = "".join([f"var {v.split(".")[0]}: Ref\n@irrelevant(\"Explicit\")\ninhale acc({v}, 1/2)\n" for v in gen_vars_ro_field]) + snippet
  snippet = "".join([f"var {v.split(".")[0]}: Ref\n@irrelevant(\"Explicit\")\ninhale acc({v})\n" for v in gen_vars_rw_field]) + snippet
  all_vars = gen_vars_ro + gen_vars_rw + gen_vars_ro_pure + gen_vars_rw_pure
  if len(all_vars) > 0:
    snippet = "var " + ", ".join([f"{v}: Int" for v in all_vars]) + "\n" + snippet

  return snippet

def apply_snippet(snippet: str, method: str):
  method_lines = method.splitlines()
  new_method = "method "
  for line in method_lines:
    if not "$PrecisionTest:" in line:
      new_method += line + "\n"
    else:
      new_method += generate_from_snippet(snippet, line) + "\n"
  return new_method


def handle_template_file(path: str, output_path: str, snippet_preamble: str, snippets: dict[str, str]):
  preamble, methods = read_test_template(path)
  if not path.endswith(".vpr"):
    return
  program_foldername = path.replace(".vpr", "").split("\\")[-1]
  os.makedirs(f"{output_path}\\{program_foldername}", exist_ok=True)
  for snippet_name, snippet in snippets.items():
    f = open(f"{output_path}\\{program_foldername}\\{snippet_name}.vpr", "w")
    f.write(preamble)
    f.write("\n")
    f.write(snippet_preamble)
    f.write("\n")
    for method in methods:
      new_method = apply_snippet(snippet, method)
      f.write(new_method)
    f.close()
    

def process_folder(folder_path: str, output_path: str, snippet_preamble: str, snippets: dict[str, str]):
  files = [os.path.join(folder_path, f) for f in os.listdir(folder_path) if os.path.isfile(os.path.join(folder_path, f))]
  for file in files:
    handle_template_file(file, output_path, snippet_preamble, snippets)

preamble, snippet_dict = read_snippets_file("silicon\\src\\test\\resources\\dependencyAnalysisTests\\benchmark_scripts\\snippets.txt")
process_folder("silicon\\src\\test\\resources\\dependencyAnalysisTests\\unitTests", 
               "silicon\\src\\test\\resources\\dependencyAnalysisTests\\precisionTests",
               preamble, snippet_dict)
