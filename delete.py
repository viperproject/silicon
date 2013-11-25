f = open('tmp/logfile.smt2')
w = open('tmp/logfile_cleaned.smt2', 'w')

stack = [[]]
level = 0

for line in f:
	split = line.split(" ")

	
	if len(split)==3 and split[0] == "(push)":
		level = level + 1			
		stack.append([])
		stack[level].append(line)
	elif len(split)==3 and split[0] == "(pop)":
		level = level - 1
		stack.pop()
	else:
		stack[level].append(line)

for i in range(len(stack)):
	for j in range(len(stack[i])):
		w.write(stack[i][j])
	
