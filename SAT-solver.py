import itertools
import sys
sys.setrecursionlimit(5000)
this_file = open("testfile.txt","r")
result_list = list()
the_numb_of_variables = 0
the_numb_of_claues = 0
for i in this_file:
    each_claues = []
    each_line = i.split()
    if each_line[0] == 'c':
        continue
    if each_line[0] == 'p':
        the_number_of_variables = int(each_line[2])
        the_number_of_claues = int(each_line[3])
        continue
    #(each_line)
    if each_line[0] != 'p':
        for j in each_line:
            if j == '0':
                continue
            if j != '0':
                each_claues.append(int(j))
    result_list.append(each_claues)
this_file.close()
def simple_sat_solve(clause_set):
    # main idea: 
    # check if clause_set from 1 to n, if not, change it form to 1 to n.
    # use 1 -> True, 0 -> False, list all posibilities.
    # reorder clause set in increasing.
    # transfer varibles into 0/1, store it in first_cluse.
    # get the result in first_cluse,(use the feature of OR) store it in second_cluse.
    # get the result in second_cluse,(use the feature of ADD), store it in final_cluse.
    # know how much variables
    all_vars = set()
    for each_clause in clause_set:
        for every_varb in each_clause:
            all_vars.add(abs(every_varb))
    total_vars = len(all_vars)
    all_vars_list = list(all_vars)
    # order list in increasing order
    reorder_list = []
    for each_variable in clause_set:
        new_cluse = sorted(each_variable, reverse=False, key=abs)
        reorder_list.append(new_cluse)
    final_order_list = []
    #order list to make sure is from 1 to n.
    for clause in reorder_list:
        order_list = []
        for variable in clause:
            if abs(variable) != all_vars_list.index(abs(variable)) + 1:
                if variable < 0:
                    order_list.append(-int(all_vars_list.index(abs(variable))) - 1)
                    continue
                if variable > 0:
                    order_list.append(int(all_vars_list.index(abs(variable))) + 1)
                    continue
            if abs(variable) == all_vars_list.index(abs(variable)) + 1:
                order_list.append(variable)
                continue
        final_order_list.append(order_list)
    # get all posibilities
    posible_values = [1, 0]
    posible_combins = itertools.product(posible_values, repeat=total_vars)
    # big process start
    final_list = []
    for combins in posible_combins:
        second_cluse = []
        # first transfer varibles into 0/1. 
        for every_cluse in final_order_list:
            first_cluse = []
            for each in every_cluse:
                if each > 0:
                    first_cluse.append(combins[each-1]) # becasue we have reordered the list, so the place is the place of 0/1
                if each < 0:    # if the variable is negative, it means we need to change 1 to 0; 0 to 1.
                    if combins[abs(each) - 1] == 0:
                        first_cluse.append(1)
                    if combins[abs(each) - 1 ] == 1:
                        first_cluse.append(0)
            # get the result in first_cluse
            if len(first_cluse) == 1:
                second_cluse.append(first_cluse[0]) # if there is only one, just add it in.
            # if is bigger than 1, then we need to consider OR feature.
            if len(first_cluse) > 1:
                if 1 in first_cluse:
                    second_cluse.append(1)
                if 1 not in first_cluse:
                    second_cluse.append(0)
        # get the result in second_cluse by using the feature of ADD.
        if 0 in second_cluse:
            continue
        if 0 not in second_cluse:
            final_list.append(combins)
    # use dic to show all possibilities.
    final_dic = {}
    key = 1
    for each in final_list:
        another_list = []
        another_dic = {}
        index = 0
        for eachone in each:
            if eachone == 0:
                another_dic[all_vars_list[index]] = 'False'
                index += 1
            if eachone == 1:
                another_dic[all_vars_list[index]] = 'True'
                index += 1
        another_list.append(another_dic)
        final_dic[key] = another_list
        key += 1
    return final_dic
def branching_sat_solve(clause_set,partial_assignment):
    # main idea: 
    # 1: copy another caluse_set to do changes like remove and original clause_set will use to do recursive.
    # 2: if a clause_set like [[2],[-2]] can get conclusion directly
    # 3: put unique variables in one list(no repeat and all are positive), this is for adding values to aprtial_assignment.
    # 4: check if partial_assignment is empty, if is: add the first value in from unique variable
    # 5: if partial_assignment is not empty,check if sat, unsat or not sure
    # 6: if is unset, back track.
    # 7: if is set,return patial_assignment.
    # 8: if is not sure, continue to build the tree.
    # Method in recursive: find all possibilities in building tree and back track, each situation has different method to treat it.
    # Method to find the next partial: find the index of last partial, and then plus one, find the variable in unique variable list.
    # create another set to store orginal clause_set
    new_clause_set = [clause[:] for clause in clause_set]
    # if clause_set like [[2],[-2]], can be say directly false
    if len(new_clause_set) == 2:
        if new_clause_set[0][0] == -new_clause_set[1][0]:
            return('UNSET')
    # store unique variables in one set, for adding new variables
    new_var = []
    # if partial_assignment has variables, need to put it head of the unique variable.
    # the aim of it is to avoid out of index problem.
    if partial_assignment != []:
        for each in partial_assignment:
            new_var.append(abs(each))
    for each_clause in new_clause_set:
        for each in each_clause:
            if abs(each) not in new_var:
                new_var.append(abs(each))
    # if no partial_assignment, then give a partial.
    if partial_assignment == []:
        partial_assignment.append(new_var[0])
        return branching_sat_solve(clause_set,partial_assignment)
    # if has, then check if is SAT
    if partial_assignment != []:
        for each in partial_assignment[:]:
            for each_clause in new_clause_set[:]: 
                if each in each_clause:
                    new_clause_set.remove(each_clause)
                elif -each in each_clause:
                    each_clause.remove(-each)
        # if is SAT, new_clause_set should be [], otherwise will continue to find partial
        if [] in new_clause_set:
            # left tree: the first variable is positive
            # if there is only one positive variable, means need to go right tree.
            if partial_assignment[0] > 0 and len(partial_assignment) == 1:
                partial_assignment[0] = -partial_assignment[0]
                return branching_sat_solve(clause_set,partial_assignment)
            # if the last partial is positive, then change last variable to minius.
            if partial_assignment[0] > 0 and partial_assignment[-1] > 0 and len(partial_assignment) <= len(new_var):
                partial_assignment[-1] = -partial_assignment[-1]
                return branching_sat_solve(clause_set,partial_assignment)
            # if the last variable is negative, then need to find the next positive variable from back and change it to minus.
            elif partial_assignment[0] > 0 and partial_assignment[-1] < 0 and len(partial_assignment) <= len(new_var):
                # delete the last element
                partial_assignment = partial_assignment[:-1]
                # track back until find the next positive variable
                while partial_assignment[-1] < 0:
                    # if the length is 1, it means its time to go top of the right side of tree
                    if len(partial_assignment) == 1:
                       partial_assignment[-1] = -partial_assignment[-1]
                       return branching_sat_solve(clause_set,partial_assignment)
                    # remove the last variable
                    partial_assignment = partial_assignment[:-1]
                # if find positive variable, make it as negative.
                if partial_assignment[-1] > 0:
                    partial_assignment[-1] = -partial_assignment[-1]
                return branching_sat_solve(clause_set,partial_assignment)
            # right tree: the first variable is negative
            # if the first variable is negative, but the length is 1, it means its unsat.
            elif partial_assignment[0] < 0 and len(partial_assignment) == 1:
                return 'UNSET'
            # if the last variable is positive, then it needs to make last variable as negative.
            elif partial_assignment[0] < 0 and partial_assignment[-1] > 0 and len(partial_assignment) <= len(new_var):
                partial_assignment[-1] = -partial_assignment[-1]
                return branching_sat_solve(clause_set,partial_assignment)
            # if the last variable is negative, then need to find the next positive variable from back and change it to minus.
            elif partial_assignment[0] < 0 and partial_assignment[-1] < 0 and len(partial_assignment) <= len(new_var):
                # delete the last variable
                partial_assignment = partial_assignment[:-1]
                # until find the next postive variable
                while partial_assignment[-1] < 0:
                   # delete negative variable 
                   partial_assignment = partial_assignment[:-1]
                   # if all variable is negative, then means its been done, and is UNSET    
                   if len(partial_assignment) == 1 or partial_assignment == []:
                       return 'UNSET'
                   else:
                       continue
                # if the last variable is positive, then make it as negative
                if partial_assignment[-1] > 0:
                    partial_assignment[-1] = -partial_assignment[-1]
                return branching_sat_solve(clause_set,partial_assignment)
        # if not sat and not unsat, still needs to build the tree:
        elif new_clause_set != []:
            # left tree: first vatiable is positive
            # if the last variableis positive, but the number of variable is full, means need to track back, change last variable to minius.
            if partial_assignment[0] > 0 and partial_assignment[-1] > 0 and len(partial_assignment) == len(new_var):
                partial_assignment[-1] = -partial_assignment[-1]
                return branching_sat_solve(clause_set,partial_assignment)
            # if the last variable is positive, and the number of variable is not full, then means still needs to add positive variables
            elif partial_assignment[0] > 0 and partial_assignment[-1] > 0 and len(partial_assignment) < len(new_var):
                index_var = new_var.index(partial_assignment[-1]) + 1
                partial_assignment.append(new_var[index_var])
                return branching_sat_solve(clause_set,partial_assignment)
            # if the last variable is negative and the number of variable is full, then means needs to track back again.
            elif partial_assignment[0] > 0 and partial_assignment[-1] < 0 and len(partial_assignment) == len(new_var):
                # delete the last element
                partial_assignment = partial_assignment[:-1]
                # track back until find the next positive variable
                while partial_assignment[-1] < 0:
                    # if the length is 1, it means its time to go top of the right side of tree
                    if len(partial_assignment) == 1:
                       partial_assignment[-1] = -partial_assignment[-1]
                       return branching_sat_solve(clause_set,partial_assignment)
                    # remove the last variable
                    partial_assignment = partial_assignment[:-1]
                # if find positive variable, make it as negative.
                if partial_assignment[-1] > 0:
                    partial_assignment[-1] = -partial_assignment[-1]
                return branching_sat_solve(clause_set,partial_assignment)
            # if the last variable is negative and the number of variable is not full,
            # means needs to continue to build the tree, add positive variable.
            elif partial_assignment[0] > 0 and partial_assignment[-1] < 0 and len(partial_assignment) < len(new_var):
                index_var = new_var.index(abs(partial_assignment[-1])) + 1
                partial_assignment.append(new_var[index_var])
                return branching_sat_solve(clause_set,partial_assignment)
            # right tree: the first variable is negative
            # if it is left top tree, but the length is 1, it means need to continue to build the tree.
            elif partial_assignment[0] < 0 and len(partial_assignment) == 1:
                index_var = new_var.index(abs(partial_assignment[0])) + 1
                partial_assignment.append(new_var[index_var])
                return branching_sat_solve(clause_set,partial_assignment)
            # if the last variable is positive and the number of variable is not full,
            # it means need to continue to build the tree.
            elif partial_assignment[0] < 0 and partial_assignment[-1] > 0 and len(partial_assignment) < len(new_var):
                index_var = new_var.index(abs(partial_assignment[-1])) + 1
                partial_assignment.append(new_var[index_var])
                return branching_sat_solve(clause_set,partial_assignment)
            # if the last variable is positive and the number of variable is full,
            # it means it needs to make last variable as negative.
            elif partial_assignment[0] < 0 and partial_assignment[-1] > 0 and len(partial_assignment) == len(new_var):
                partial_assignment[-1] = -partial_assignment[-1]
                return branching_sat_solve(clause_set,partial_assignment)
            # if the last variable is negative and the number of variable is full,
            # it means its time to track back.
            elif partial_assignment[0] < 0 and partial_assignment[-1] < 0 and len(partial_assignment) == len(new_var):
                # delete the last variable
                partial_assignment = partial_assignment[:-1]
                # until find the next postive variable
                while partial_assignment[-1] < 0:
                   # delete negative variable 
                   partial_assignment = partial_assignment[:-1]
                   # if all variable is negative, then means its been done, and is UNSET    
                   if len(partial_assignment) == 1 or partial_assignment == []:
                       return 'UNSET'
                   else:
                       continue
                # if the last variable is positive, then make it as negative
                if partial_assignment[-1] > 0:
                    partial_assignment[-1] = -partial_assignment[-1]
                return branching_sat_solve(clause_set,partial_assignment)
            # if the last variable is negative and the number of variables not full,
            # It means we need to continue to complete the tree
            elif partial_assignment[0] < 0 and partial_assignment[-1] < 0 and len(partial_assignment) < len(new_var):
                index_var = new_var.index(abs(partial_assignment[-1])) + 1
                partial_assignment.append(new_var[index_var])
                return branching_sat_solve(clause_set,partial_assignment)
        # if new_clause_set is [], then is SET.
        elif new_clause_set == []:
            return partial_assignment
def unit_propagate(clause_set):
    unit_clause = []
    neg_unit_clause = []
    new_clause_set = [] # aim set
    # find the unit clause
    for clause in clause_set:
        if len(clause) == 1:
            unit_clause = int(clause[0])
            neg_unit_clause = int(-clause[0])
        else:
            continue
    # following unit propagate,
    for clause in clause_set:
        new_variable_set = []
        # if there is unit clause and the length is not 1, then delete whole clause.
        if unit_clause in clause:
            continue
        else:
            for varibale in clause:
                # if there is negation unit clause, then delete it as well, but keep the other parts
                if varibale == neg_unit_clause:
                    continue
                else:
                    # keep the other parts
                    new_variable_set.append(varibale)
        # store it in new clause set.
        new_clause_set.append(new_variable_set)
    # if the output clause is same, then say not able to fix it.
    if clause_set == new_clause_set:
        return new_clause_set
    # if the output is [], then it means finished 
    if new_clause_set == []:
        return []
    # if the output is [[]], then it means finsihed as well
    if new_clause_set == [[]] or [] in new_clause_set:
        return [[]]
    # if not above, continue!
    return unit_propagate(new_clause_set)
def pure_literal_eliminate(clause_set):
    pure_variable = []
    # if there is one clause, it means satisfiable
    if len(clause_set) == 1 and clause_set != [[]] and [] not in clause_set:
        return []
    if clause_set == [[]] or [] in clause_set:
        return False
    # count how many pure variable in the clause_set
    pure_count = 0
    # make a list to help find pure variable
    clause_list = set()
    # this set is to store final answer
    new_pure_set = []
    # add variables in the set, but no repeat number
    for clause in clause_set:
        for variable in clause:
            clause_list.add(variable)
    clause_list = sorted(clause_list,reverse=False, key=abs)
    # find pure variable
    for variable in clause_list:
        negative_variable = -variable
        # if is pure variable
        if negative_variable not in clause_list:
            # if more than two pure variable
            if pure_count != 0:
                # if failed at beginning
                if new_pure_set == []:
                    return 0
                # if failed after that
                else:
                    return new_pure_set
            # if just one pure variable
            if pure_count == 0:
                pure_count += 1
                pure_variable = variable
                break
        # if not pure variable
        if negative_variable in clause_list:
            continue
    # if there is no pure variable
    if pure_count == 0:
        return clause_set
    # follow pure literal eliminate process
    for clause in clause_set:
        # if pure variable in the clause, then dont store.
        if pure_variable in clause:
            continue
        # if not, store it in new_pure_set
        if pure_variable not in clause:
            new_pure_set.append(clause)
    # continue to find it.
    return pure_literal_eliminate(new_pure_set)
def dpll_sat_solve(clause_set,partial_assignment):
    # main idea:
    # 1: main structure is still the branching_sat_solve
    # 2: make a new partial to store partial in unit_propagate and pure_literal_eliminate
    # 3: changes on unit_propagate and pure_literal_eliminate is to make it can return: new_clause,unit(i.e new partial),ifIsSAT(true or false).
    # 4: general structure:
        # 1: make a copy of clause set.
        # 2: quick check.
        # 3: make unique variable.
        # 4: add partial assignment
        # 5: first check if is sat or unsat or need to continue(first simplify)
        # 6: second check by using unit_propagate(second simplify)
        # 7: if is sat, then make new_partial and make clause_set as empty; if is unsat, then reorder new partial.
        # 7: third check by using pure_literal_eliminate(third simplify)
        # 8: if is sat, then make new_partial and make clause_set as empty; if is unsat, then reorder new partial.
        # 9: if is unsat or needs to continue, then go recursive.
        # 10: if is sat, then add new_partial to partial, then output.
    # new partial
    new_partial = []
    # build a set to delete in future
    new_clause_set = [clause[:] for clause in clause_set]
    # if clause_set like [[2],[-2]], can be say directly false
    if len(new_clause_set) == 2:
        if new_clause_set[0][0] == -new_clause_set[1][0]:
            return('UNSET')
    # store unique variables in one set, for adding new variables
    new_var = []
    if partial_assignment != []:
        for each in partial_assignment:
            new_var.append(abs(each))
    for each_clause in new_clause_set:
        for each in each_clause:
            if abs(each) not in new_var:
                new_var.append(abs(each))
    # if no partial_assignment, then give a partial.
    if partial_assignment == []:
        partial_assignment.append(new_var[0])
        return dpll_sat_solve(clause_set,partial_assignment)
    # if has, then check if is SAT
    elif partial_assignment != []:
        for each in partial_assignment[:]:
            for each_clause in new_clause_set[:]: 
                if each in each_clause:
                    new_clause_set.remove(each_clause)
                elif -each in each_clause:
                    each_clause.remove(-each)
        # apply unit propagate
        def dpll_unit_propagate(clause_set,unit):
            unit_clause = []
            neg_unit_clause = []
            new_clause_set = [] # aim set
            # find the unit clause
            for clause in clause_set:
                if len(clause) == 1:
                    unit_clause = int(clause[0])
                    unit.append(int(clause[0]))
                    neg_unit_clause = int(-clause[0])
                else:
                    continue
            # following unit propagate,k
            for clause in clause_set:
                new_variable_set = []
                # if there is unit clause and the length is not 1, then delete whole clause.
                if unit_clause in clause:
                    continue
                else:
                    for varibale in clause:
                        # if there is negation unit clause, then delete it as well, but keep the other parts
                        if varibale == neg_unit_clause:
                            continue
                        else:
                            # keep the other parts
                            new_variable_set.append(varibale)
                # store it in new clause set.
                new_clause_set.append(new_variable_set)
            # if the output clause is same, then say not able to fix it.
            if clause_set == new_clause_set:
                return new_clause_set,unit,False
            # if the output is [], then it means finished 
            if new_clause_set == []:
                return [],unit,True
            # if the output is [[]], then it means finsihed as well
            if new_clause_set == [[]] or [] in new_clause_set:
                return [[]],unit,False
            # if not above, continue!
            return dpll_unit_propagate(new_clause_set,unit)
    # if is sat, then make new_clause_set as empty, add new_partial
    if dpll_unit_propagate(clause_set,[])[2] == True:
       new_clause_set = []
       new_partial = dpll_unit_propagate(new_clause_set,[])[1]
    # if is unsat or need to continue, add new_partial
    if dpll_unit_propagate(clause_set,[])[2] == False:
       new_clause_set,new_partial,new_sign = dpll_unit_propagate(new_clause_set,[])
       new_partial = list(set(new_partial))
    # apply pure_literal_eliminate
    def dpll_pure_literal_eliminate(clause_set,unit):
        pure_variable = []
        # if there is one clause, it means satisfiable
        if len(clause_set) == 1 and clause_set != [[]] and [] not in clause_set:
            unit.append(clause_set[0][0])
            return [],unit,True
        if clause_set == [[]] or [] in clause_set:
            return [[]],unit,False
        # count how many pure variable in the clause_set
        pure_count = 0
        # make a list to help find pure variable
        clause_list = set()
        # this set is to store final answer
        new_pure_set = []
        # add variables in the set, but no repeat number
        for clause in clause_set:
            for variable in clause:
                clause_list.add(variable)
        clause_list = sorted(clause_list,reverse=False, key=abs)
        # find pure variable
        for variable in clause_list:
            negative_variable = -variable
            # if is pure variable
            if negative_variable not in clause_list:
                # if more than two pure variable
                if pure_count != 0:
                    # if failed at beginning
                    if new_pure_set == []:
                        return 0
                    # if failed after that
                    else:
                        return new_pure_set
                # if just one pure variable
                if pure_count == 0:
                    pure_count += 1
                    pure_variable = variable
                    unit.append(pure_variable)
                    break
            # if not pure variable
            if negative_variable in clause_list:
                continue
        # if there is no pure variable
        if pure_count == 0:
            return clause_set,unit,False
        # follow pure literal eliminate process
        for clause in clause_set:
            # if pure variable in the clause, then dont store.
            if pure_variable in clause:
                continue
            # if not, store it in new_pure_set
            if pure_variable not in clause:
                new_pure_set.append(clause)
        # continue to find it.
        return dpll_pure_literal_eliminate(new_pure_set,unit)
    # if is sat, then make new_clause_set as empty, add new_partial
    if dpll_pure_literal_eliminate(clause_set,[])[2] == True:
       new_clause_set = []
       new_partial_pure = dpll_pure_literal_eliminate(new_clause_set,[])[1]
       for clause in new_partial_pure:
           new_partial.append(clause)
    # if is unsat or need to continue, add new_partial
    if dpll_pure_literal_eliminate(clause_set,[])[2] == False:
       new_clause_set,new_pure_partial,new_sign = dpll_pure_literal_eliminate(new_clause_set,[])
       for clause in new_pure_partial:
           new_partial.append(clause)
       new_partial = list(set(new_partial))
    # if is sat, then put new_partial in partial, and output
    if new_clause_set == []:
        # put new_partial in partial
        for clause in new_partial:
            partial_assignment.append(clause)
        partial_assignment = sorted(partial_assignment,reverse=False, key=abs)
        return partial_assignment
    # if is unsat, then back track
    elif [] in new_clause_set:
        # left tree: first variable is positive:
        # if at top of left tree, then go right tree
        if partial_assignment[0] > 0 and len(partial_assignment) == 1:
            partial_assignment[0] = -partial_assignment[0]
            return dpll_sat_solve(clause_set,partial_assignment)
        # if the last variable is positive, then change last variable to minius.
        if partial_assignment[0] > 0 and partial_assignment[-1] > 0 and len(partial_assignment) <= len(new_var):
            partial_assignment[-1] = -partial_assignment[-1]
            return dpll_sat_solve(clause_set,partial_assignment)
        # if the last variable is negative, then need to find the next positive variable and make it to negative
        elif partial_assignment[0] > 0 and partial_assignment[-1] < 0 and len(partial_assignment) <= len(new_var):
            # delete the last element
            partial_assignment = partial_assignment[:-1]
            # track back until find the next positive variable
            while partial_assignment[-1] < 0:
                # if the length is 1, it means its time to go top of the right side of tree
                if len(partial_assignment) == 1:
                    partial_assignment[-1] = -partial_assignment[-1]
                    return dpll_sat_solve(clause_set,partial_assignment)
                # remove the last variable
                partial_assignment = partial_assignment[:-1]
            # if find positive variable, make it as negative.
            if partial_assignment[-1] > 0:
                partial_assignment[-1] = -partial_assignment[-1]
            return dpll_sat_solve(clause_set,partial_assignment)
        # right tree: first variable is negative
        # if the length is 1, it means need to stop
        elif partial_assignment[0] < 0 and len(partial_assignment) == 1:
            return 'UNSET'
        # if the last variable is positive, then means it needs to make last variable as negative.
        elif partial_assignment[0] < 0 and partial_assignment[-1] > 0 and len(partial_assignment) <= len(new_var):
            partial_assignment[-1] = -partial_assignment[-1]
            return dpll_sat_solve(clause_set,partial_assignment)
        # if the last variable is negative, then find the next positive variable and make it as negative.
        elif partial_assignment[0] < 0 and partial_assignment[-1] < 0 and len(partial_assignment) <= len(new_var):
            # delete the last variable
            partial_assignment = partial_assignment[:-1]
            # until find the next postive variable
            while partial_assignment[-1] < 0:
                # delete negative variable 
                partial_assignment = partial_assignment[:-1]
                # if all variable is negative, then means its been done, and is UNSET    
                if len(partial_assignment) == 1 or partial_assignment == []:
                    return 'UNSET'
                else:
                    continue
            # if the last variable is positive, then make it as negative
            if partial_assignment[-1] > 0:
                partial_assignment[-1] = -partial_assignment[-1]
            return dpll_sat_solve(clause_set,partial_assignment)
    # need to continue to build the tree
    elif new_clause_set != []:
        # left tree: first variable is positive:
        # if the last variable is positive, but the number of variable is full, means need to track back, change last variable to minius.
        if partial_assignment[0] > 0 and partial_assignment[-1] > 0 and len(partial_assignment) == len(new_var):
            partial_assignment[-1] = -partial_assignment[-1]
            return dpll_sat_solve(clause_set,partial_assignment)
        # if the last variable is positive, and the number of variable is not full, then means still needs to add positive variables
        elif partial_assignment[0] > 0 and partial_assignment[-1] > 0 and len(partial_assignment) < len(new_var):
            index_var = new_var.index(partial_assignment[-1]) + 1
            partial_assignment.append(new_var[index_var])
            return dpll_sat_solve(clause_set,partial_assignment)
        # if the last variable is negative and the number of variable is full, means needs to track back again.
        elif partial_assignment[0] > 0 and partial_assignment[-1] < 0 and len(partial_assignment) == len(new_var):
            # delete the last element
            partial_assignment = partial_assignment[:-1]
            # track back until find the next positive variable
            while partial_assignment[-1] < 0:
                # if the length is 1, it means its time to go top of the right side of tree
                if len(partial_assignment) == 1:
                    partial_assignment[-1] = -partial_assignment[-1]
                    return dpll_sat_solve(clause_set,partial_assignment)
                # remove the last variable
                partial_assignment = partial_assignment[:-1]
            # if find positive variable, make it as negative.
            if partial_assignment[-1] > 0:
                partial_assignment[-1] = -partial_assignment[-1]
            return dpll_sat_solve(clause_set,partial_assignment)
        # if the last variable is negative and the number of variable is not full, means needs to continue to build the tree, add positive variable.
        elif partial_assignment[0] > 0 and partial_assignment[-1] < 0 and len(partial_assignment) < len(new_var):
            index_var = new_var.index(abs(partial_assignment[-1])) + 1
            partial_assignment.append(new_var[index_var])
            return dpll_sat_solve(clause_set,partial_assignment)
        # right tree: first variable is negative
        # if the first variable is negative, but the length is 1, it means need to continue to go right side of the tree.
        elif partial_assignment[0] < 0 and len(partial_assignment) == 1:
            index_var = new_var.index(abs(partial_assignment[0])) + 1
            partial_assignment.append(new_var[index_var])
            return dpll_sat_solve(clause_set,partial_assignment)
        # if the last variable is positive and the number of variable is not full, it means need to continue to go left side of the tree.
        elif partial_assignment[0] < 0 and partial_assignment[-1] > 0 and len(partial_assignment) < len(new_var):
            index_var = new_var.index(abs(partial_assignment[-1])) + 1
            partial_assignment.append(new_var[index_var])
            return dpll_sat_solve(clause_set,partial_assignment)
        # if the last variable is positive and the number of variable is full,it means it needs to make last variable as negative.
        elif partial_assignment[0] < 0 and partial_assignment[-1] > 0 and len(partial_assignment) == len(new_var):
            partial_assignment[-1] = -partial_assignment[-1]
            return dpll_sat_solve(clause_set,partial_assignment)
        # if the last variable is negative and the number of variable is full, it means its time to track back.
        elif partial_assignment[0] < 0 and partial_assignment[-1] < 0 and len(partial_assignment) == len(new_var):
            # delete the last variable
            partial_assignment = partial_assignment[:-1]
            # until find the next postive variable
            while partial_assignment[-1] < 0:
                # delete negative variable 
                partial_assignment = partial_assignment[:-1]
                # if all variable is negative, then means its been done, and is UNSET    
                if len(partial_assignment) == 1 or partial_assignment == []:
                    return 'UNSET'
                else:
                    continue
            # if the last variable is positive, then make it as negative
            if partial_assignment[-1] > 0:
                partial_assignment[-1] = -partial_assignment[-1]
            return dpll_sat_solve(clause_set,partial_assignment)
        # if the last variable is negative and the number of variable not full,
        # It means we need to continue to complete the tree
        elif partial_assignment[0] < 0 and partial_assignment[-1] < 0 and len(partial_assignment) < len(new_var):
            index_var = new_var.index(abs(partial_assignment[-1])) + 1
            partial_assignment.append(new_var[index_var])
            return dpll_sat_solve(clause_set,partial_assignment)
# result: [-1, 2, 3, 4, -5, -6, 7], the name of dicmac file is testfile.txt.