
from copy import deepcopy
from collections import defaultdict

class FOL:

	def __init__(self,total_query, queries, kB_size, kB):
		self.total_query = total_query
		self.queries = queries
		self.kB_size = kB_size
		self.kB = kB
		self.count = 0
		self.tellKb = []
		self.predicateMap = {}
		self.query_pred_arg= []
		self.RepeatedPred = defaultdict(list)



	def tell(self):
		temp_rule_set = []
		for rule in self.kB:
			literal = rule.split("|")
			temp_rule = []
			predicate_list = []
			for lit in literal:
				predicate = lit[:lit.find("(")]
				negated_prediate = '~' + predicate if predicate[0] != '~' else predicate[1:]
				arguments = lit[lit.find("(") + 1 :lit.find(")") ].split(",")
				for ind, val in enumerate(arguments):
					if self.isVariable(val): 
						arguments[ind] = arguments[ind] + str(self.count)
				temp_rule.append([predicate, arguments])
				self.predicateMap[predicate] = self.predicateMap.get(predicate ,[]) + [[arguments, self.count]]
				if negated_prediate in predicate_list :
					self.RepeatedPred[self.count].append([predicate, False])
				predicate_list.append(predicate)			
			temp_rule_set.append([self.count] + temp_rule)
			self.count += 1
		self.kB = temp_rule_set

		

	def isVariable(self, s):
		return True if s[0].islower() else False


	def isNegative(self, s):
		return True if s[0] == '~' else False


	def negateQueryGetArg(self, query):
		predicate =  query[1 :query.find("(")] if self.isNegative(query) else '~' + query[:query.find("(")]
		arguments = query[query.find("(") + 1 :query.find(")") ].split(",")
		return [predicate, arguments]


	def unify(self, param1, param2, sigma):	
		if sigma == False :return False
		elif param1 == param2 and len(param1) == 1 and len(param2) == 1 : return sigma
		elif len(param1) > 1 and len(param2) > 1  : return self.unify(param1[1:], param2[1:],self.unify([param1[0]], [param2[0]], sigma))
		elif self.isVariable(param1[0]) : return self.unifyVar(param1[0], param2[0], sigma)
		elif self.isVariable(param2[0]) : return self.unifyVar(param2[0], param1[0], sigma)
		else: return False


	def unifyVar(self, param1, param2, sigma):
		if sigma == False : return sigma
		elif param1 in sigma : return self.unify(sigma[param1], param2, sigma)
		elif param2 in sigma : return self.unify(param1, sigma[param2], sigma)
		else:
			new_sigma = sigma.copy()
			new_sigma[str(param1)] = param2
			return new_sigma


	def occur_check( var1, var2):
		return True if var1 == var2 else False



	def substitue(self, t_rule, sigma):
		for index, value in enumerate(t_rule[1]):
			if value in sigma:	t_rule[1][index] = sigma[value]
		#return rule



	def isAlreadyVisted(self, visited, new_rule, copy = True):
		res = False
		currentRule = ""
		for literal in new_rule:
			currentRule += literal[0]
			for args in literal[1] :
				currentRule += args if not self.isVariable(args) else "$$"
		if currentRule in visited : res = True
		if copy : visited.append(currentRule)
		return res	
		if currentRule in visited : 
			if copy == True : visited.append(currentRule)
			return True
		return False



	def isRepeated(self, pred, rule_no, repeated_list):
		#return False
		if rule_no in repeated_list:
			if [pred, True] in repeated_list[rule_no] :
				return True 
			if [pred, False] in repeated_list[rule_no] :
				repeated_list[rule_no].remove([pred, False])
				repeated_list[rule_no].append([pred, True])
		return False



	def resolution(self, query):
		new_set_of_rules = [[self.negateQueryGetArg(query)]]
		#print new_set_of_rules
		self.kB.append([self.count, new_set_of_rules[0][0]])	
		self.predicateMap[new_set_of_rules[0][0][0]] = self.predicateMap.get(new_set_of_rules[0][0][0] ,[]) \
														+ [[new_set_of_rules[0][0][1], self.count]]

		
		visited = []	
		i = 0
		repeated_list = deepcopy(self.RepeatedPred)
		while i < 20000:
			#print i
			#print "new_set_of_rules", new_set_of_rules
			#print new_set_of_rules ,""
			if not new_set_of_rules: return False
			literals = new_set_of_rules.pop()
			
			self.isAlreadyVisted(visited, literals, True )
			for lit in literals:
				predicate, arguments = lit
				searchForPredicate = predicate[1:] if self.isNegative(predicate) else '~' + predicate[:]
				if searchForPredicate not in self.predicateMap: continue
				for pred_arg in self.predicateMap[searchForPredicate]:
					if self.isRepeated(searchForPredicate, pred_arg[1], repeated_list) : continue
					sigma = self.unify(arguments, pred_arg[0], {})
					if sigma != False:
						temp_rule = deepcopy(lit)
						self.substitue(temp_rule, sigma)
						subs_arg = temp_rule[1]
						new_rule = []
						flag = False
						for rule in literals:
							#print"literal rule:" , rule
							temp_rule = deepcopy(rule)
							self.substitue(temp_rule, sigma)
							if temp_rule[0] == predicate and temp_rule[1] == subs_arg and flag == False: 
								flag = True
								continue
							if temp_rule not in new_rule: new_rule.append(temp_rule)						
						flag = False
						for rule in self.kB[pred_arg[1]][1:]:
							
							temp_rule = deepcopy(rule)
							self.substitue(temp_rule, sigma)					
							if temp_rule[0] == searchForPredicate  and temp_rule[1] == subs_arg and flag == False:
								flag = True
								continue 							
							if temp_rule not in new_rule:new_rule.append(temp_rule)
						if new_rule == [] : 										
							return True
						if not self.isAlreadyVisted(visited,new_rule, False ):
						
							new_set_of_rules.append(new_rule)
						#print new_set_of_rules
		
			i += 1		
		return False



	def Inference(self):
		self.tell()
		result =[]
		for query  in self.queries:
			#print "*************** new query ***************"
			#print self.kB
			isSuccssful =self.resolution(query)
			if isSuccssful == True :result.append("TRUE")
			else: result.append("FALSE")
			self.kB.pop()
		return result




# this will parse the given input file
def parse_input():

	# open input file
	input_file = "input.txt"
	with open(input_file,'r') as inp: 

		# get all the contents of the file in variable content
		contents = [x.strip('\n') for x in inp.readlines()]
		total_query = int(contents[0])

		# remaining content is matrix for board
		queries = []
		for line in contents[1: total_query + 1 ]:
			queries.append(line.replace(" ",""))

		kB_size = int(contents[total_query + 1])
		kB = []
		for line in contents[total_query + 2 :]:
			kB.append(line.replace(" ",""))

	# return all values to main function
	return total_query, queries, kB_size, kB



# write the output in output file
def write_ouput(result):

	# open output file
	out_file =  "output.txt"
	with open(out_file, 'w') as out: 
		for i in result:
			out.write(str(i) + "\n")
		


# main function
def main():

		# parse input file to get the input variables
		total_query, queries, kB_size, kB = parse_input()
		result = FOL(total_query, queries, kB_size, kB).Inference()
		write_ouput(result)


if __name__ == '__main__':
	main()
