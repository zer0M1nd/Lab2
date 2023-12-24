from copy import deepcopy


class LIA_Constrain:
    def __init__(self, constrains, func_args, trans_table, syn_expr, logic_type, var_symbol):
        #print("constrains:",constrains)
        #print("func_args:",func_args)
        #print("trans_table:",trans_table)
        #print("syn_expr:",syn_expr)
        #print("logic_type:",logic_type)
        #print("var_symbol:",var_symbol)
        self.parent_map = {}

        self.possible_expr = None
        self.conditions = []
        self.compares = []
        self.consts = []

        self.compare_op = ['<', '<=', '>=', '>']
        self.condition_op = ['and', '=>']
        self.exchange_op = ['+', '*', '=', 'and', 'or']

        self.func_args = func_args
        self.trans_table = trans_table
        self.logic_type = logic_type
        self.var_symbol = var_symbol

        constrains_ = deepcopy(constrains)
        self.translate(constrains_)
        self.build_parent_map(constrains_)

        for constrain in constrains_:
            self.extract(constrain)
        print(self.conditions)
        print(self.compares)
        print(self.consts)
        self.final_expr = self.gen()
    
    def translate(self,stmt):
        if isinstance(stmt,list):
            for i in range(len(stmt)):
                ret=self.translate(stmt[i])
                if ret is not None:
                    stmt[i]=ret
        elif isinstance(stmt,str):
            if stmt in self.trans_table:
                return self.trans_table[stmt]
        return None

    def build_parent_map(self,stmts):
        for i in stmts:
            if isinstance(i,list):
                self.parent_map[str(i)]=stmts
                self.build_parent_map(i)

    def have_func(self,stmt):
        if not isinstance(stmt,list) and stmt==self.func_args[0]:
            return True
        elif isinstance(stmt,list):
            for i in stmt:
                if self.have_func(i):
                    return True
        return False
    
    def extract(self,stmt):
        func_flag = True
        func_pos = -1
        for i in range(len(stmt)):
           if isinstance(stmt[i],list):
               func_flag=False
               f=self.extract(stmt[i])
               if f: 
                   func_pos=i

        if func_pos>0:
            if func_pos != 1:
                another_pos=1
            else:
                another_pos=2
            
            if stmt[0]=='<' or stmt[0]=='>' or stmt[0]=='>=' or stmt[0]=='<=':
                if isinstance(stmt[another_pos],tuple):
                    another_stmt=str(stmt[another_pos][1])
                else:
                    another_stmt=stmt[another_pos]
                if another_pos==1:
                    d={"<":">",">":"<",">=":"<=","<=":">="}
                    self.compares.append((d[stmt[0]],another_stmt))
                else:
                    self.compares.append((stmt[0],another_stmt))

            elif stmt[0]=='=':
                if isinstance(stmt[another_pos],tuple):
                    another_stmt=str(stmt[another_pos][1])
                else:
                    another_stmt=stmt[another_pos]
                if another_stmt != None:
                    if not self.have_func(another_stmt):
                        if str(stmt) in self.parent_map:
                            parent_stmt=self.parent_map[str(stmt)]
                            if parent_stmt[0] == 'and' or parent_stmt[0]=='=>': #"=>是什么?"
                                if parent_stmt[1]!=stmt:
                                    cond_stmt=parent_stmt[1]
                                else:
                                    cond_stmt=parent_stmt[2]
                                self.conditions.append((cond_stmt,another_stmt))
                            else:
                                self.possible_expr=another_stmt
                        else:
                            self.possible_expr=another_stmt
        
        if not func_flag:
            return False
        
        const_flag=True
        argument_list=list()
        for i in range(1,len(self.func_args)):
            if isinstance(stmt[i],tuple):
                substmt=str(stmt[i][1])
            else:
                substmt=stmt[i]
            if substmt.isdigit():
                if self.logic_type == 'LIA':
                    argument_list.append(substmt)
                else:
                    pass #BV不写了
            else:
                const_flag = False
                break
        if (const_flag==True) and (str(stmt) in self.parent_map):
            parent_stmt=self.parent_map[str(stmt)]
            if parent_stmt[0]=='=':
                if parent_stmt[1] !=stmt:
                    another_stmt=parent_stmt[1]
                else:
                    another_stmt=parent_stmt[2]
                if isinstance(another_stmt,tuple):
                    another_stmt=str(another_stmt[1])
                

                if self.logic_type=='LIA':
                    self.consts.append((argument_list,another_stmt))
                else:
                    pass
        
        for i in range(len(self.func_args)):
            if stmt[i]!=self.func_args[i]:
                return False
        return True

    def process_cond(self,size):
        new_stmt=[]
        cur_stmt=new_stmt
        if size>0:
            for i in range(size):
                cur_stmt+=['ite',*self.conditions[i]]
                next_stmt=[]
                cur_stmt.append(next_stmt)
                cur_stmt=next_stmt
        return cur_stmt,new_stmt
    
    def process_cmp(self,size):
        new_stmt=[]
        cur_stmt=new_stmt
        if size>0:
            for i in range(size):
                cond=[]
                stmt=self.compares[i][1]
                cur=cond
                cond_cnt=0
                for j in range(len(self.compares)):
                    if i!=j:
                        
                        if cond_cnt != size-1:
                            cur.append("and")
                            cur.append([self.compares[j][0],stmt,self.compares[j][1]])
                            next_cond=[]
                            cur.append(next_cond)
                            cur=next_cond
                        else:
                            cur+=[self.compares[j][0],stmt,self.compares[j][1]]
                        cond_cnt+=1
                cur_stmt += ['ite',cond,stmt] 
                next_stmt=[]
                cur_stmt.append(next_stmt)
                cur_stmt = next_stmt
        return cur_stmt,new_stmt
                            
    def process_const(self,size):
        new_stmt=[]
        cur_stmt=new_stmt
        if size>0:
            for i in range(size):
                argument,stmt=self.consts[i]
                cond=[]
                cur=cond
                cond_count=0
                for j in range(len(argument)):
                    if cond_count==len(argument)-1:
                        cur+=['=',self.func_args[j+1],argument[j]]
                    else:
                        cur.append('and')
                        cur.append(['=',self.func_args[j+1],argument[j]])
                        next_cond=[]
                        cur.append(next_cond)
                        cur=next_cond
                    cond_count+=1
                cur_stmt+=['ite',cond,stmt]
                next_stmt=[]
                cur_stmt.append(next_stmt)
                cur_stmt=next_stmt
        return cur_stmt,new_stmt


    def gen(self):
        ret=None
        ret_cur=None

        if len(self.conditions) > 0:

            if len(self.compares) >0 or len(self.consts) >0:
                cur_stmt,new_stmt=self.process_cond(len(self.conditions))
            else:
                cur_stmt,new_stmt=self.process_cond(len(self.conditions)-1)
                cur_stmt.append(self.conditions[-1][1])

            ret_cur=cur_stmt
            if ret==None:
                ret=new_stmt
            print(1,new_stmt,cur_stmt)

        if len(self.compares) > 0:
            if len(self.conditions) >0:
                cur_stmt,new_stmt=self.process_cmp(len(self.compares))
            else:
                cur_stmt,new_stmt=self.process_cmp(len(self.compares)-1)
                cur_stmt.append(self.compares[-1][1])
            if ret_cur != None:
                ret_cur.append(new_stmt[:])
            ret_cur=cur_stmt
            if ret==None:
                ret=new_stmt
            print(2,new_stmt,cur_stmt)
        
        if len(self.consts)>0:
            if self.possible_expr != None:
                cur_stmt,new_stmt=self.process_const(len(self.consts))
            else:
                cur_stmt,new_stmt=self.process_const(len(self.consts)-1)
                cur_stmt.append(self.consts[-1][1])
            if ret_cur !=None:
                ret_cur.append(new_stmt[:])
            ret_cur=cur_stmt
            if ret==None:
                ret=new_stmt
            print(3,new_stmt,cur_stmt)
        
        if len(self.conditions)==0 and len(self.compares)==0 and len(self.consts)==0:
            if self.possible_expr !=None:
                new_stmt=[self.possible_expr]
                if ret_cur!=None:
                    ret_cur.append(new_stmt[:])
                if ret==None:
                    ret=new_stmt
        #print(ret)
        return ret

        


                         
             
    


