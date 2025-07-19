
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
  for decl in var_decls:
    tmp = decl.split("=")
    if(tmp[0] == "$READ_ONLY"):
      read_only_vars = read_only_vars + tmp[1].split(",")
    elif(tmp[0] == "$READ_WRITE"):
      read_write_vars = read_write_vars + tmp[1].split(",")
  # print(f"line: {line}")
  # print(f"read only: {read_only_vars}")
  # print(f"read write: {read_write_vars}")
  # print()
  return read_only_vars, read_write_vars

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
  read_only_vars, read_write_vars = extract_vars(line)
  snippet, gen_vars_ro_field = replace_vars(snippet, "$RO_INT_FIELD_", [v for v in read_only_vars if "." in v])
  snippet, gen_vars_rw_field = replace_vars(snippet, "$RW_INT_FIELD_", [v for v in read_write_vars if "." in v])
  snippet, gen_vars_ro = replace_vars(snippet, "$RO_INT_", read_only_vars)
  snippet, gen_vars_rw = replace_vars(snippet, "$RW_INT_", read_write_vars)
  snippet = "".join([f"var {v.split(".")[0]}: Ref\n@irrelevant(\"Explicit\")\ninhale acc({v}, 1/2)\n" for v in gen_vars_ro_field]) + snippet
  snippet = "".join([f"var {v.split(".")[0]}: Ref\n@irrelevant(\"Explicit\")\ninhale acc({v})\n" for v in gen_vars_rw_field]) + snippet
  all_vars = gen_vars_ro + gen_vars_rw
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


def handle_template_file(path, snippet_preamble, snippets: dict[str, str]):
  preamble, methods = read_test_template(path)
  os.makedirs(path.replace(".vpr", ""), exist_ok=True)
  for snippet_name, snippet in snippets.items():
    f = open(path.replace(".vpr", f"\\{snippet_name}.vpr"), "w")
    f.write(preamble)
    f.write("\n")
    f.write(snippet_preamble)
    f.write("\n")
    for method in methods:
      new_method = apply_snippet(snippet, method)
      f.write(new_method)
    f.close()
    

preamble, snippet_dict = read_snippets_file("silicon\\src\\test\\resources\\dependencyAnalysisTests\\generation\\snippets.txt")
print(preamble)

handle_template_file("silicon\\src\\test\\resources\\dependencyAnalysisTests\\unitTests\\permissions.vpr",
                     preamble, snippet_dict)
