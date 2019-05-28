#!/usr/bin/env python2
# -*- coding: utf-8 -*-
from __future__ import division
import sys
import nltk
import string
import pdb
import copy
import re
import gen_derived_tree
import math
from operator import itemgetter
from nltk.tokenize import word_tokenize
import math
import string
import random
import json
import os
import platform
change_dir = False
if os.getcwd()[-8:] == 'Autobank':
    os.chdir('MGParse')
    change_dir = True
sys.path.append('./SuperSuperTagger/scripts/supertagging')
sys.path.append('./MGParse/SuperSuperTagger/scripts/supertagging')
#try:
    #import Supertagger
#except ImportError:
    #print "Warning: Failed to import the LSTM Supertagger!"
if change_dir:
    os.chdir('../')
import argparse
from timeout import timeout
from decimal import *
try:
    from fibonacci_heap_mod import Fibonacci_heap
except ImportError:
    sys.stderr.write("\nWarning: Failed to import Fibonacci_heap!")
from timeit import default_timer
sys.setrecursionlimit(10000)
brackets='()'
open_b, close_b = brackets
open_pattern, close_pattern = (re.escape(open_b), re.escape(close_b))
node_pattern = '[^%s%s]+' % (open_pattern, close_pattern)
leaf_pattern = '[^%s%s]+' % (open_pattern, close_pattern)
punctuation = string.punctuation
punctuation+="``"
punctuation+="..."
punctuation+=" "
punctuation = re.sub('%', '', punctuation)
punctuation = re.sub('&', '', punctuation)
punctuation = re.sub('\$', '', punctuation)
punctuation = re.sub('/', '', punctuation)
punctuation = re.sub(':', '', punctuation)
punctuation = re.sub(';', '', punctuation)
punctuation = re.sub('-', '', punctuation)
punctuation = re.sub("'", "", punctuation, count=1000)
punctuation = re.sub('@', '', punctuation)
not_cat_feature = re.compile('=|(\+)|(\-)|~|≈|(\^)|&|\?|!|\>|\<')
cat_pattern = re.compile('\w+')
current_id = 0
chart_size = 0
outside_costs = {}
current_cost = -9999999999
current_lowest = None

class Expression:
    def __init__(self, cat_feature = None, head_string=None, head_features = [], checked_features = [], head_span = [], separator = "::", ID=None, inside_cost=0, outside_cost=0, is_overt=None):
        if head_string != None:
            try:
                head_string = head_string.decode('utf8')
            except UnicodeDecodeError:
                x=0
            i = -1
            for feature in head_features:
                i+=1
                try:
                    decoded_feature = feature.encode('utf8')
                except UnicodeDecodeError:
                    decoded_feature = feature
                head_features[i] = decoded_feature
        self.head_string = head_string
        #self.pointers contains a list of two membered tuples, the first member pointing to the head child
        #the second to the non-head child.  The system will not add identical items to the chart but it will add their
        #pointers to the item already in the chart
        self.pointers = []
        self.non_head_chains = []
        self.head_chain = Chain(cat_feature = cat_feature, head_string = self.head_string, features = head_features, checked_features = checked_features, head_span = head_span)
        #self.sc indicates whether the expression is a head (simple = ::) or larger constituent (complex = :)
        self.sc = separator
        #we need each chain to have a separator, but only for the purposes of drawing
        #derivation trees.. therefore, I just set them to the single derived separator from the
        #beginning, and use the expression's sc when drawing the head chain
        if separator == '::':
            self.head_chain.sc = ':'
        elif separator == ':\u0305:\u0305' or separator == ':\\u0305:\\u0305':
            self.head_chain.sc = ':\u0305'
        self.cat_feature = cat_feature
        if inside_cost != 0:
            self.inside_cost = Decimal(math.log10(inside_cost)*-1)
        else:
            self.inside_cost = Decimal(inside_cost)
        self.head_chain.head_inside_cost = self.inside_cost
        self.outside_cost = Decimal(outside_cost)
        self.total_cost = Decimal(self.inside_cost+self.outside_cost)
        self.persist_selectee = False
        self.derivation_bracketing = None
        self.remove_from_chart = False
        self.saturated = False
        self.licensees = []#used only in cases of lexical head coordination
        self.was_coordinator = False
        self.is_overt = is_overt
        if ID != None:
            ID = str(ID)
        self.ID = ID
        if head_string != None:
            #otherwise this class was called with empty attributes in the copy_expression function
            self.exp_signature = generate_exp_signature(self)
            
    def __hash__(self):
        generate_exp_signature(self).__hash__()

    def print_exp(self):
        #prints out the lexical heads of each chain in the expression and their features and the narrow yield.. thus any words whose features are all
        #checked will not appear as heads, while heads which have moved out of a given chain still appear as lexical heads of that chain
        print "Head chain: "
        full_features = get_full_features(self.head_chain)
        try:
            print tuple([YIELD.get_string() for part in self.head_chain.string.narrow_yield.get_string() for YIELD in part]), tuple([YIELD.get_span() for part in self.head_chain.string.narrow_yield.get_string() for YIELD in part]), full_features
            print "Non-head chains:"
            if len(self.non_head_chains) == 0:
                print "None"
            else:
                for chain in self.non_head_chains:
                    full_features = get_full_features(chain)
                    print chain.string.narrow_yield.get_string(), chain.string.narrow_yield.get_span(), full_features
        except AttributeError:
            print self.head_chain.string.narrow_yield.get_string(), self.head_chain.string.narrow_yield.get_span(), full_features
            print "Non-head chains:"
            if len(self.non_head_chains) == 0:
                print "None"
            else:
                for chain in self.non_head_chains:
                    full_features = get_full_features(chain)
                    print chain.string.narrow_yield.get_string(), chain.string.narrow_yield.get_span(), full_features

def get_full_features(chain):
    full_features = []
    f_index = -1
    for feature in chain.features:
        f_index+=1
        if len(chain.subcatAgreeFeatures[f_index]) > 0:
            #we need to insert the subcat features after the cat feature, e.g. d, and before any following
            #diacritic, e.g. =
            index = -1
            foundStart = False
            full_feature = feature
            for char in feature:
                index+=1
                if char not in ['\xe2', '=', '+', '-', '~', '≈', '^', '&', '?', '!', '>', '<']:
                    foundStart = True
                elif foundStart == True:
                    featureSuffix = feature[index:]
                    full_feature = feature[0:index]+"{"+".".join([f for f in chain.subcatAgreeFeatures[f_index]])+"}"+featureSuffix
                #in case there was no feature suffix we do the following
            if '{' not in full_feature:
                full_feature = feature+"{"+".".join([f for f in chain.subcatAgreeFeatures[f_index]])+"}"
        else:
            full_feature = feature
        full_features.append(full_feature)
    return full_features

class Chain:
    def __init__(self, cat_feature = None, head_string='', features=[], checked_features = [], head_span=[]):
        self.string = String(head_string=head_string, head_span=head_span)
        (syn_features, subcatAgreeFeatures) = self.syn_subcatAgreeFeatures(features)
        self.features = syn_features
        self.subcatAgreeFeatures = subcatAgreeFeatures
        self.checked_features = checked_features
        self.head_string = head_string
        self.cat_feature = cat_feature
        i=-1
        self.cat_subcats = []
        for feature in self.features:
            i+=1
            if not not_cat_feature.search(feature):
                self.cat_subcats = self.subcatAgreeFeatures[i]
        self.covert = False
        self.overt_movement_required = False
        self.inside_cost = Decimal(0)
        self.head_inside_cost = Decimal(0)
        
    def syn_subcatAgreeFeatures(self, features):
        syn_features = []
        subcatAgreeFeatures = []
        for feature in features:
            subcatAgreeFeature = subcatAgreeFeatures_pat.search(feature)
            if subcatAgreeFeature:
                sf = subcatAgreeFeature.group(0)[1:-1].split(".")
                sf.sort()
                subcatAgreeFeatures.append(sf)
            else:
                subcatAgreeFeatures.append([])
            syn_features.append(re.sub(subcatAgreeFeatures_pat, "", feature))
        return (syn_features, subcatAgreeFeatures)

class String:
    def __init__(self, head_string='', head_span=[], narrow_yield_span=[]):
        #initially we keep head separate from left and right dependents for head movement
        self.head_yield = [Yield(head_string, head_span)]
        self.l_dependent_yields = [Yield(u'\u03b5', [[],[]])]
        self.r_dependent_yields = [Yield(u'\u03b5', [[],[]])]
        #for narrow yield, the string part is a list composed of the yield objects of the three parts, while the narrow
        #yield is initially set to the narrow yield of the head, since these are the same for lexical items..
        self.narrow_yield = Yield([self.l_dependent_yields, self.head_yield, self.r_dependent_yields], head_span)

class Yield:
    def __init__(self, string, span):
        self.string = string
        self.span = span

    def set_string(self, new_string):
        self.string = new_string

    def get_string(self):
        return self.string

    def set_span(self, new_span):
        self.span = new_span

    def get_span(self):
        return self.span

    def set_yield(self, new_string, new_span):
        self.string = new_string
        self.span = new_span

    def get_yield(self):
        return (self.string, self.span)

feature_mapping = {'+':['-'], '-':['+'], '':['≈', '='], '=':[''], '≈':['']}
extraposition_hosts = []
sel_variables = ['x', 'y', 'z', 'w']
agreement_features = ['1SG', '2SG', '3SG', '1PL', '2PL', '3PL']
case_features = ['NOM', 'ACC', 'GEN']#do not include DAT in this paradigm as it will mix with the case subcat of the object of [dat] P
paradigms = [case_features, agreement_features]
                 
#define reg expressions for each selector feature
right_merge = re.compile('\w+=')
right_merge_left_h_move = re.compile('>\w+=')
right_merge_right_h_move = re.compile('\w+<=')
#left_merge will be used both for left-merged complements and for all externally merged specifiers - though of
#course the actual merge subrule which applies in these two cases will differ..
left_merge = re.compile('=\w+')
left_merge_left_h_move = re.compile('=>\w+')
left_merge_right_h_move = re.compile('=\w+<')
right_merge_x_h_move = re.compile('\w+=\^')
left_merge_x_h_move = re.compile('=\w+\^')
left_adjoin = re.compile('\w+≈')
right_adjoin = re.compile('≈\w+')
subcatAgreeFeatures_pat = re.compile('{.*}')
sentence_length = None

null_heads = []

#The following are the features that intervene for relativized smc.. they should all be lower cased
Abar_features = ['-foc', '-top', '-wh']
A_features = ['-tough', 'd', '-case', '-epp', '-num', '-pers', '-loc']
A2_features = ['-self', '-num', '-pers', '-epp', '-loc']
Abar2_features = ['t~', 'v~', 'c~', '-n']#at the moment, we are limiting rightward movement to t, v, c only.. to change this you must add the licensee feature here (and in gen_derived_tree, where you must also modify the re right_move) and also add the licensor to extraposition_hosts both here and in autobankGUI
multiple_agree_features = ['-num', '-pers', '-epp', '-loc']#in some constructions, such as expletive 'there' and locative inversion, we decompose T and its goal's case features into their component phi and epp feature.. we need at most two of the features in this group to be simultaneously active
covert_only_movers = ['-pol', '-negs']
overt_only_movers = ['-foc', '-top', '-n', 'd', '-tough', '-epp']#these types of movement can only proceed in overt fashion
type_raisers = []
#invalidate derivations with) chains with any of the value features as their first feature.
covert_move_on = True
chart = []
agenda_signatures = {}
supertag_links = {}
moveable_spans = None
source_spans = None
maxMoveDist = None
hybrid_mode = False

def time_taken(end_time):
    end_time = int(end_time)
    mins = int(end_time / 60)
    hours = int(mins / 60)
    if hours != 0:
        mins = mins - (hours * 60)
    secs = end_time % 60
    if hours == 1:
        HOUR = "hour"
    else:
        HOUR = "hours"
    if mins == 1:
        MIN = "minute"
    else:
        MIN = "minutes"
    if secs == 1:
        SEC = "second"
    else:
        SEC = "seconds"
    if hours != 0:
        return str(hours)+" "+HOUR+", "+str(mins)+" "+MIN+" and "+str(secs)+" "+SEC+".."
    elif mins != 0:
        return str(mins)+" "+MIN+" and "+str(secs)+" "+SEC+".."
    else:
        if secs == 0:
            return "less than a second.."
        return str(secs)+" "+SEC+".."

def unpack_supertags(supertags, lexicon, null_heads):
    #supertag_links contains unique IDs for MG categories as keys and another dictionary
    #as value, where the keys of the second dictionary are the indices for the checked features
    #of that category and their values are the IDs of the other category doing the checking
    #IDs are only unique within each supertag when they arrive, which has to be the case so that we can
    #recognize the same tag across trees for doing corpus counts, but we need them to be globally
    #unique during parsing..
    global supertag_links
    global current_id
    for supertag in supertags:
        inside_cost = supertag[1]
        supertag = supertag[0]
        if type(supertag[0]) == type(()):
            #if this is just an atomic category it must be overt and we just add
            #it straight into lexicon
            supertag[1] = current_id
            lexicon.append((supertag, inside_cost))
            current_id += 1
        else:
            old_id_new_id_mappings = {}
            for merge_link in supertag:
                if merge_link[0][1] not in old_id_new_id_mappings:
                    old_id_new_id_mappings[merge_link[0][1]] = current_id
                    current_id += 1
                #now change the old id into the new globally unique id
                merge_link[0][1] = old_id_new_id_mappings[merge_link[0][1]]
                if merge_link[2][1] not in old_id_new_id_mappings:
                    old_id_new_id_mappings[merge_link[2][1]] = current_id
                    current_id += 1
                #now change the old id into the new globally unique id
                merge_link[2][1] = old_id_new_id_mappings[merge_link[2][1]]
            for merge_link in supertag:
                if str(merge_link[0][1]) not in supertag_links:
                    supertag_links[str(merge_link[0][1])] = {str(merge_link[1]):str(merge_link[2][1])}
                else:
                    supertag_links[str(merge_link[0][1])][str(merge_link[1])] = str(merge_link[2][1])
                if str(merge_link[2][1]) not in supertag_links:
                    supertag_links[str(merge_link[2][1])] = {str(merge_link[3]):str(merge_link[0][1])}
                else:
                    supertag_links[str(merge_link[2][1])][str(merge_link[3])] = str(merge_link[0][1])
                if merge_link[0][0][0][0] == '[' and merge_link[0][0][0][-1] == ']':
                    if merge_link[0] not in null_heads:
                        null_heads.append(merge_link[0])
                else:
                    if (merge_link[0], inside_cost) not in lexicon:
                        lexicon.append((merge_link[0], inside_cost))
                if merge_link[2][0][0][0] == '[' and merge_link[2][0][0][-1] == ']':
                    if merge_link[2] not in null_heads:
                        null_heads.append(merge_link[2])
                else:
                    if (merge_link[2], lex_score) not in lexicon:
                        lexicon.append((merge_link[2], lex_score))

def main(sentence, show_trees = True, print_expressions = True, return_bracketings = False,
         return_xbar_trees = False, LEXICON=None, CovertLexicon=None, ExtraposerLexicon=None,
         TypeRaiserLexicon=None, ToughOperatorLexicon=None, NullExcorporatorLexicon=None,
         allowMoreGoals=True, printPartialAnalyses=False, limitRightwardMove=True,
         terminal_output=None, terminal_output_name=None, supertags=None,
         lexical_scoring=True, start_time=None, MOVEABLE_SPANS=None,
         MAXMOVEDIST=None, null_c_lexicon=None, SOURCE_SPANS=None, vp_ellipsis=True):
    #A* MG parser takes as input a string and returns the viterbi parse
    global type_raisers
    global extraposition_hosts
    global lexicon
    global extraposers
    global TYPE_RAISERS
    global tough_functions
    global covert_lexicon
    global null_excorporators
    global null_heads
    global covert_move_on
    global chart
    global strategy
    global current_id
    global supertag_links
    global moveable_spans
    global source_spans
    global chart_size
    global maxMoveDist
    global hybrid_mode
    global outside_costs
    global SENTENCE_LENGTH
    global current_cost
    global current_lowest
    if null_c_lexicon != None:
        hybrid_mode = True
    maxMoveDist = MAXMOVEDIST
    chart_size = 0
    moveable_spans = MOVEABLE_SPANS
    if start_time == None:
        start_time = default_timer()
    supertag_links.clear()
    agenda_signatures.clear()
    supertag_links = {}
    current_id = 0
    lexicon = []
    #for some reason lexicon and null_heads were sometimes persisting from a previous parse, despite recreating them here.
    del(lexicon[:])
    null_heads = []
    del(null_heads[:])
    del(chart[:])
    while len(type_raisers) > 0:
        del(type_raisers[0])
    sys.stderr.write("\n\n*******************************************************")
    sys.stderr.write("\n\nParsing sentence: "+sentence+"\n")
    unpack_supertags(supertags, lexicon, null_heads)
    covert_move_on = True
    extraposition_hosts = ['t', 'v', 'p', 'd', 'D', 'c']
    sentence = re.sub("''", '"', sentence, count=1000)
    sentence = re.sub("&", "ANDANDAND", sentence, count=5)
    sentence = re.sub("%", "PERCENTPERCENT", sentence, count=5)
    tok_sentence = word_tokenize(sentence)
    i=-1
    for word in tok_sentence:
        i+=1
        tok_sentence[i] = re.sub("ANDANDAND", "&", tok_sentence[i], count=5)
        tok_sentence[i] = re.sub("PERCENTPERCENT", "%", tok_sentence[i], count=5)
    tok_sentence = [w.lower() for w in tok_sentence if (w not in punctuation and w != "''")]
    agenda = Fibonacci_heap()
    sentence_length = len(tok_sentence)
    SENTENCE_LENGTH = sentence_length
    if SOURCE_SPANS != None:
        source_spans = {}
        for i in range(sentence_length):
            source_spans[i] = []
        for span in SOURCE_SPANS:
            source_spans[span[0]].append(span)
    else:
        source_spans = None
    for i in range(sentence_length+1):
        chart.append([])
        for j in range(sentence_length+1):
            chart[i].append({})
            chart[i][j]['signatures'] = {}
    chart[0][-1]['goal'] = []
    precompute_outside_costs(lexicon, sentence_length)        
    mg_cats_count = 0
    i=-1
    sys.stderr.write("\nInserting overt axioms into agenda and null axioms into chart...")
    if terminal_output != None:
        terminal_output.write("\nInserting overt axioms into agenda and null axioms into chart...")
    for i in range(sentence_length+1):
    #fill agenda up with all possible overt atomic items in this position
        if i != len(tok_sentence):
            for head in lexicon:
                if head[0][2] == i:
                    inside_cost = Decimal(head[1])
                    outside_cost = Decimal(0)
                    if head[0][2] != 0:
                        outside_cost += Decimal(outside_costs[(0,head[0][2])])
                    if head[0][2]+1 != sentence_length:
                        outside_cost += Decimal(outside_costs[(head[0][2]+1, sentence_length)])
                    head = head[0]
                    mg_cats_count += 1
                    if 'conj' in head[0][2]:
                        separator = ":\u0305:\u0305"
                    else:
                        separator = "::"
                    HEAD = Expression(cat_feature = head[0][2], head_string = head[0][0], head_features = head[0][1], head_span = [i, i+1], separator=separator, ID=head[1], inside_cost=inside_cost, outside_cost=outside_cost, is_overt=True)
                    add_to_agenda(HEAD, agenda)
                    SATURATED_HEAD = type_saturate(HEAD)
                    if SATURATED_HEAD != None:
                        add_to_agenda(SATURATED_HEAD, agenda)
    #first, if this is the hybrid atomic-supertag approach, we add all the atomic null c heads..
    if null_c_lexicon != None:
        for null_head in null_c_lexicon:
            if 'conj' in null_head[2]:
                separator = ":\u0305:\u0305"
            else:
                separator = "::"
            NULL_HEAD = Expression(cat_feature = null_head[2], head_string = null_head[0], head_features = null_head[1], head_span = [[], []], separator=separator, ID=current_id, is_overt=False)
            current_id += 1
            add_to_chart(NULL_HEAD, sentence_length, agenda)
    #next, we add all the null heads which are anchored to a supertag..
    NULL_HEADS = []
    for null_head in null_heads:
        if 'conj' in null_head[0][2]:
            separator = ":\u0305:\u0305"
        else:
            separator = "::"
        NULL_HEAD = Expression(cat_feature = null_head[0][2], head_string = null_head[0][0], head_features = null_head[0][1], head_span = [[], []], separator=separator, ID=null_head[1], is_overt=False)
        NULL_HEADS.append(NULL_HEAD)
    for NULL_HEAD in NULL_HEADS:
        add_to_chart(NULL_HEAD, sentence_length, agenda)
    tag_word = "supertags"
    sys.stderr.write("\nInitialized chart with "+str(float("{0:.2f}".format(mg_cats_count/sentence_length)))+" "+tag_word+" on average per word for this sentence..")
    if terminal_output != None:
        terminal_output.write("\nInitialized chart with "+str(float("{0:.2f}".format(mg_cats_count/sentence_length)))+" "+tag_word+" on average per word for this sentence..")
    i = -1
    c_goal_found = False
    printed_beam_message = False
    while not c_goal_found:
        i+=1
        while len(agenda) > 0:
            entry = agenda.dequeue_min()
            trigger_item = entry.get_value()
            cst = entry.get_priority()
            current_cost = cst
            current_lowest = (trigger_item, trigger_item.total_cost)
            if len(trigger_item.head_chain.features) == 1 or allowMoreGoals:
                #if we are allowing non-c goals we will allow elements which still have
                #selector features to check but not licensors as we still ban
                #items containing moving chains from being goals so these licensors can never be checked..
                if check_goal(item = trigger_item, agenda = agenda, sentence_length = sentence_length,allowMoreGoals=allowMoreGoals):
                    c_goal_found = True
                    break
            #if the trigger_item has a licensor (movement trigger) as its first feature, we execute this movement
            #and place the resulting item in the agenda.. no need to put such items in the chart at all..
            #Everything else goes into the chart
            adjoin_or_coord_only = False
            if '+' in trigger_item.head_chain.features[0]:
                #we don't need to check the side of + as this is movement to spec, which is always leftward
                move(trigger_item = trigger_item, agenda = agenda, direction = 'left', printPartialAnalyses=printPartialAnalyses)
                continue
            elif trigger_item.head_chain.features[0] in ['=d', '=D']:
                CONTINUE = [False]
                move(trigger_item = trigger_item, agenda = agenda, direction = 'left', CONTINUE = CONTINUE, printPartialAnalyses=printPartialAnalyses)
                if CONTINUE[0]:
                    continue
            elif trigger_item.head_chain.features[0] in extraposition_hosts and len(trigger_item.non_head_chains) > 0:
                CONTINUE = [False]
                move(trigger_item = trigger_item, agenda = agenda, direction = 'right', CONTINUE = CONTINUE, printPartialAnalyses=printPartialAnalyses)
                if CONTINUE[0]:
                    #if rightward movement licensee was present, we do not allow this trigger item to enter merge except adjoin merge and coordination or where the selector is the [dat] head (so rightward movement and adjunction can interleave in any order - both are adjunction after all, and we can have atb rightward movement for coordination (i.e. to outer TP not inner one) - coordination of DP being really coordination of [dat] PP)
                    adjoin_or_coord_only = True
            add_to_chart(trigger_item = trigger_item, agenda = agenda, sentence_length = sentence_length, adjoin_or_coord_only=adjoin_or_coord_only, printPartialAnalyses=printPartialAnalyses)
            #as well as adding this item to the chart, if this item has an extraposition_host feature as its first
            #feature, we send it to move
        break
    end_time = default_timer() - start_time
    sys.stderr.write("\nFinished Parsing...")
    sys.stderr.write("\nTime taken: "+time_taken(end_time))
    sys.stderr.write("\nFinal size of chart: "+str(chart_size)+" entries")
    sys.stderr.write("\nNow searching for suitable goals...")
    if terminal_output != None:
        terminal_output.write("\nFinished Parsing...")
        terminal_output.write("\nTime taken: "+time_taken(end_time))
        terminal_output.write("\nFinal size of chart: "+str(chart_size))
        terminal_output.close()
        terminal_output = open(terminal_output_name, 'a')
    derivation_bracketings = []
    subcat_derivation_bracketings = []
    full_derivation_bracketings = []
    subcat_full_derivation_bracketings = []
    derived_bracketings = []
    xbar_bracketings = []
    xbar_trees = []
    inside_costs = []
    Cgoals = []
    goalsToDelete = []
    mainClauseFound = False
    saturated_goals = []
    for goal in chart[0][sentence_length]['goal']:
        #if there are saturated fragments we only allow these, not unsaturated fragments
        if not not_cat_feature.search(goal.head_chain.features[0]):
            saturated_goals.append(goal)
    if len(saturated_goals) > 0:
        chart[0][sentence_length]['goal'] = saturated_goals             
    for item in chart[0][sentence_length]['goal']:
        if item.head_chain.features[0] in ['c', 'C']:
            Cgoals.append(item)
            if 'MAIN' in item.head_chain.subcatAgreeFeatures[0]:
                mainClauseFound = True
    if mainClauseFound:
        #if there are main clauses in goals, then we get rid of any subordinate clause
        #goals..
        for item in chart[0][sentence_length]['goal']:
            if item.head_chain.features[0] in ['c', 'C']:
                if 'MAIN' not in item.head_chain.subcatAgreeFeatures[0]:
                    goalsToDelete.append(item)
    for goal in goalsToDelete:
        chart[0][sentence_length]['goal'].remove(goal)
        Cgoals.remove(goal)
    fragment_goals = False
    if allowMoreGoals and len(Cgoals) == 0:
        #if allowMoreGoals is true AND there are no goals with c as their feature, we
        #allow any category which spans the sentence to be a goal..
        #and since all c goals can only have 1 feature left, we only allow fragments
        #if there are no c goals..  this should prevent random pro being inserted at
        #the fringe of a constituent
        fragment_goals = True
        goals = chart[0][sentence_length]['goal']
    else:
        goals = Cgoals
    if len(goals) > 0:
        message = "\nFound suitable goal(s).. Now unpacking the chart and building trees..\n"
        sys.stderr.write("\n"+message)
        if terminal_output != None:
            terminal_output.write(message)
            terminal_output.close()
            terminal_output = open(terminal_output_name, 'a')
    for item in goals:
        item.derivation_bracketings = []
        item.full_derivation_bracketings = []
        item.subcat_derivation_bracketings = []
        item.subcat_full_derivation_bracketings = []
        (subcat_derivation_bracketing, subcat_full_derivation_bracketing) = generate_derivation_bracketing(item, "", "")
        subcat_derivation_bracketing = re.sub('@COMMA@', ';', subcat_derivation_bracketing, count = 10000)
        subcat_full_derivation_bracketing = re.sub('@COMMA@', ';', subcat_full_derivation_bracketing, count = 10000)
        derivation_bracketing = re.sub('{.*?}', '', subcat_derivation_bracketing, count = 100000)
        full_derivation_bracketing = re.sub('{.*?}', '', subcat_full_derivation_bracketing, count = 100000)
        item.derivation_bracketings.append(derivation_bracketing)
        item.full_derivation_bracketings.append(full_derivation_bracketing)
        item.subcat_derivation_bracketings.append(subcat_derivation_bracketing)
        item.subcat_full_derivation_bracketings.append(subcat_full_derivation_bracketing)
    #we want to limit the amount of rightward movement to an absolute minimum and ban any parses with vacuous rightward movement
    #we can do this by counting the number of [extraposers] in each parse, if any, and then eliminating any parses with
    #a greater number than the minimum.
    items_to_keep = []
    if limitRightwardMove:
        min_extraposers = 999999999
        for item in goals:
            for derivation_bracketing in item.derivation_bracketings:
                num_extraposers = derivation_bracketing.count("[extraposer]")
                if num_extraposers < min_extraposers:
                    min_extraposers = num_extraposers
                    min_extraposers = max(1, min_extraposers)
        item_index = -1
        total_items = 0
        for item in goals:
            item_index += 1
            bracketing_index = -1
            for derivation_bracketing in item.derivation_bracketings:
                total_items += 1
                bracketing_index += 1
                num_extraposers = derivation_bracketing.count("[extraposer]")
                if num_extraposers <= min_extraposers:
                    items_to_keep.append((item_index, bracketing_index))
        if len(items_to_keep) < total_items:
            sys.stderr.write("\nRemoving "+str((total_items)-len(items_to_keep))+" items with the greatest number of [extraposers]..\n")
    else:
        item_index = -1
        for item in goals:
            item_index += 1
            bracketing_index = -1
            for derivation_bracketing in item.derivation_bracketings:
                bracketing_index += 1
                items_to_keep.append((item_index, bracketing_index))
    i = 0
    if len(items_to_keep) == 1:
        sys.stderr.write("\nExtracted 1 parse from chart..\n")
    else:
        sys.stderr.write("\nExtracted "+str(len(items_to_keep))+" parses from chart..\n")
    for item in items_to_keep:
        i += 1
        if i % 10 == 0:
            sys.stderr.write("\nProcessing parse number: "+str(i))
        if print_expressions == True:
            print ""
            print "Goal expression:"
            goals[item[0]].print_exp()
            print ""
        subcat_derivation_bracketing = goals[item[0]].subcat_derivation_bracketings[item[1]]
        subcat_full_derivation_bracketing = goals[item[0]].subcat_full_derivation_bracketings[item[1]]
        derivation_bracketing = goals[item[0]].derivation_bracketings[item[1]]
        full_derivation_bracketing = goals[item[0]].full_derivation_bracketings[item[1]]
        try:
            subcat_derivation_bracketing = subcat_derivation_bracketing.encode('utf8')
            derivation_bracketing = derivation_bracketing.encode('utf8')
            subcat_full_derivation_bracketing = subcat_full_derivation_bracketing.encode('utf8')
            full_derivation_bracketing = full_derivation_bracketing.encode('utf8')
        except UnicodeDecodeError:
            x=0
        sdb = " ".join("".join(fix_coord_annotation(subcat_derivation_bracketing).split(" ")).split("##"))
        db = " ".join("".join(fix_coord_annotation(derivation_bracketing).split(" ")).split("##"))
        sfdb = " ".join("".join(fix_coord_annotation(subcat_full_derivation_bracketing).split(" ")).split("##"))
        fdb = " ".join("".join(fix_coord_annotation(full_derivation_bracketing).split(" ")).split("##"))
        derivation_bracketings.append(db)
        full_derivation_bracketings.append(fdb)
        subcat_full_derivation_bracketings.append(sfdb)
        subcat_derivation_bracketings.append(sdb)
        #we feed the derivation tree bracketing to the module "gen_derived_tree" and this constructs the derived tree
        #from it..
        while "  " in sfdb:
            sfdb = re.sub("  ", " ", sfdb, count=10000)
        while "  " in sfdb:
            fdb = re.sub("  ", " ", sfdb, count=10000)
        if return_xbar_trees == False:
            (derived_bracketing, xbar_bracketing) = gen_derived_tree.main(db, allowMoreGoals=allowMoreGoals)
        else:
            (derived_bracketing, xbar_bracketing, xbar_tree) = gen_derived_tree.main(db, return_xbar_tree=True, allowMoreGoals=allowMoreGoals)
            xbar_trees.append(xbar_tree)
        derived_bracketings.append(derived_bracketing)
        xbar_bracketings.append(xbar_bracketing)
        if show_trees == True:
            print "Derivation Tree: "
            print "("+re.sub("\(", " (", sdb[1:], count = 10000)
            print ""
            try:
                derivation_tree = nltk.Tree.parse(db, remove_empty_top_bracketing=True, leaf_pattern=leaf_pattern, node_pattern=node_pattern)
                subcat_derivation_tree = nltk.Tree.parse(sdb, remove_empty_top_bracketing=True, leaf_pattern=node_pattern, node_pattern=node_pattern)
            except AttributeError:
                derivation_tree = nltk.Tree.fromstring(db, remove_empty_top_bracketing=True, leaf_pattern=leaf_pattern, node_pattern=node_pattern)
                subcat_derivation_tree = nltk.Tree.fromstring(sdb, remove_empty_top_bracketing=True, leaf_pattern=leaf_pattern, node_pattern=node_pattern)
            subcat_derivation_tree.draw()
            print "Full Derivation Tree: "
            print "("+re.sub("\(", " (", sfdb[1:], count = 10000)
            print ""
            try:
                full_derivation_tree = nltk.Tree.parse(fdb, remove_empty_top_bracketing=True, leaf_pattern=leaf_pattern, node_pattern=node_pattern)
                subcat_full_derivation_tree = nltk.Tree.parse(sfdb, remove_empty_top_bracketing=True, leaf_pattern=leaf_pattern, node_pattern=node_pattern)
            except AttributeError:
                full_derivation_tree = nltk.Tree.fromstring(fdb, remove_empty_top_bracketing=True, leaf_pattern=leaf_pattern, node_pattern=node_pattern)
                subcat_full_derivation_tree = nltk.Tree.fromstring(sfdb, remove_empty_top_bracketing=True, leaf_pattern=leaf_pattern, node_pattern=node_pattern)
            subcat_full_derivation_tree.draw()
            print "Derived Tree:"
            print derived_bracketing
            print ""
            try:
                derived_tree = nltk.Tree.parse(derived_bracketing, remove_empty_top_bracketing=True, leaf_pattern=leaf_pattern, node_pattern=node_pattern)
            except AttributeError:
                derived_tree = nltk.Tree.fromstring(derived_bracketing, remove_empty_top_bracketing=True, leaf_pattern=leaf_pattern, node_pattern=node_pattern)
            derived_tree.draw()
            print "Xbar Tree:"
            print xbar_bracketing
            print ""
            try:
                xbar_tree = nltk.Tree.parse(xbar_bracketing, remove_empty_top_bracketing=True, leaf_pattern=leaf_pattern, node_pattern=node_pattern)
            except AttributeError:
                xbar_tree = nltk.Tree.fromstring(xbar_bracketing, remove_empty_top_bracketing=True, leaf_pattern=leaf_pattern, node_pattern=node_pattern)
            xbar_tree.draw()
            print "****************************************************************************"
    return (end_time, derivation_bracketings, derived_bracketings, xbar_bracketings, xbar_trees, subcat_derivation_bracketings, subcat_full_derivation_bracketings, full_derivation_bracketings, inside_costs)

def precompute_outside_costs(lexicon, sentence_length):
    global outside_costs
    for i in range(sentence_length):
        for j in range(sentence_length):
            if j < i:
                continue
            outside_costs[(i,j+1)] = None
    #first we will populate the table with the lowest costs for axioms
    for item in lexicon:
        item_index = item[0][2]
        item_cost = Decimal(math.log10(item[1])*-1)
        if outside_costs[(item_index, item_index+1)] == None or outside_costs[(item_index, item_index+1)] > item_cost:
            outside_costs[(item_index, item_index+1)] = item_cost
    #now we do the larger spans
    for i in range(sentence_length):
        for j in range(sentence_length):
            if j <= i:
                continue
            else:
                span_length = j+1-i
                span_cost = Decimal(0)
                for k in range(span_length):
                    span_cost += Decimal(outside_costs[(i+k, i+k+1)])
            outside_costs[(i,j+1)] = Decimal(span_cost)
            
def type_saturate(head):
    if head.ID in supertag_links:
        if str(len(head.head_chain.checked_features)) in supertag_links[head.ID]:
            return None
    if head.was_coordinator:
        #this is a constituent that already started life as a lexical coordinator
        #and was then transformed back to a lexical head :: category.. so we don't want to be
        #able to type saturate this item..
        return None
    if head.sc != "::":
        return None
    if head.head_chain.head_string[0] == '[' and head.head_chain.head_string[-1] == ']':
        #disallowing coordination of covert heads (if you ever change this you will have to make sure that [xxx] is coverted to epsilon)
        return None
    s_head = copy_expression(head)
    s_head.sc = ":"
    f_index = -1
    cat_feature = None
    for feature in s_head.head_chain.features:
        f_index += 1
        if not not_cat_feature.search(feature):
            cat_feature = feature
            break
    if cat_feature == None:
        #must be an adjunctizer so cannot be coordinated
        return None
    subcat_features = head.head_chain.subcatAgreeFeatures[f_index]
    purged_subcat_features = []
    for f in subcat_features:
        if f not in sel_variables:
            purged_subcat_features.append(f)
    s_head.head_chain.subcatAgreeFeatures = [purged_subcat_features]
    s_head.head_chain.oldSubcatAgreeFeatures = copy.deepcopy(head.head_chain.subcatAgreeFeatures)
    s_head.saturated = True
    if f_index > 0:
        for f in s_head.head_chain.features[:f_index]:
            s_head.head_chain.checked_features.append(f)
        del(s_head.head_chain.features[:f_index])
    #we want to disallow type saturation of already saturated heads, e.g.
    #unergative verbs (assuming these are true intransitives) because this would lead
    #to spurious ambiguity (i.e. two analyses of coordinated unergatives, one phrasal coordination
    #the other lexical head coordination
    if len(s_head.head_chain.checked_features) == 0:
        return None
    if len(s_head.head_chain.features) > 1:
        for f in s_head.head_chain.features[1:]:
            s_head.licensees.append(f)
        del(s_head.head_chain.features[1:])
    s_head.pointers = [({'operation':'type_saturation'}, head)]
    s_head.exp_signature = generate_exp_signature(s_head)
    return s_head

def fix_coord_annotation(db):
    #this amends the bracketing so that :̅:̅ shows up correctly when the tree is displayed.
    while ':\\u0305:\\u0305' in db:
        start = db.index(':\\u0305:\\u0305')
        db = db[0:start]+':\xcc\x85:\xcc\x85'+db[start+14:]
    while ':\\u0305' in db:
        start = db.index(':\\u0305')
        db = db[0:start]+':\xcc\x85'+db[start+7:]
    while ':\u0305:\u0305' in db:
        start = db.index(':\u0305:\u0305')
        db = db[0:start]+':\xcc\x85:\xcc\x85'+db[start+14:]
    while ':\u0305' in db:
        start = db.index(':\u0305')
        db = db[0:start]+':\xcc\x85'+db[start+7:]
    return db
    
def generate_derivation_bracketing(expression, subcat_derivation_bracketing="", subcat_full_derivation_bracketing=""):
    #takes as input an expression object from the chart (should generally be a goal item) and
    #generates its derivation tree bracketing
    addSubCatFeatures(expression)
    try:
        #json mucks things up by converting everything to unicode..
        #we need to convert things to utf8 to combine all the strings successfully,
        #but then later we convert back to unicode to display the trees, otherwise
        #the ≈ symbols don't come out properly..
        expression.head_string = expression.head_string.encode('utf8')
    except UnicodeDecodeError:
        x=0
    if (expression.sc == "::" or expression.sc == ":\u0305:\u0305") and not expression.was_coordinator:
        try:
            subcat_derivation_bracketing = subcat_derivation_bracketing.encode('utf8')
            subcat_full_derivation_bracketing = subcat_full_derivation_bracketing.encode('utf8')
        except UnicodeDecodeError:
            x=0
        if expression.sc == "::":
            subcat_derivation_bracketing += "("+'\xce\xb5'+";##"+expression.head_string+";##"+'\xce\xb5'+"##::##"+"##".join(expression.head_chain.features)+") "
            subcat_full_derivation_bracketing += "("+'\xce\xb5'+";##"+expression.head_string+";##"+'\xce\xb5'+"##::##"+"##".join(expression.head_chain.features)+") "
        elif expression.sc == ":\u0305:\u0305":
            subcat_derivation_bracketing += "("+'\xce\xb5'+";##"+expression.head_string+";##"+'\xce\xb5'+"##:\u0305:\u0305##"+"##".join(expression.head_chain.features)+") "
            subcat_full_derivation_bracketing += "("+'\xce\xb5'+";##"+expression.head_string+";##"+'\xce\xb5'+"##:\u0305:\u0305##"+"##".join(expression.head_chain.features)+") "
        return subcat_derivation_bracketing, subcat_full_derivation_bracketing
    elif expression.sc == ":" or (expression.sc == "::" and expression.was_coordinator):
        try:
            STRING = "##".join(expression.head_chain.string.narrow_yield.get_string().encode('utf8').split(" "))
            if STRING == '\xce\xb5':
                STRING = ""
            STRING = re.sub("@COMMA@$", "", STRING, count=10000)
            STRING = re.sub("##$", "", STRING, count=10000)
            STRING = re.sub("@COMMA@$", "", STRING, count=10000)
            STRING = re.sub("^@COMMA@##", "", STRING, count=10000)
            STRING = re.sub("##@COMMA@", "", STRING, count=10000)
            STRING = re.sub("@COMMA@##:", "##:", STRING, count=10000)
            if STRING == "":
                STRING = '\xce\xb5'
            try:
                subcat_full_derivation_bracketing += "("+STRING.encode('utf8')+"##"+expression.sc+"##"+"##".join(expression.head_chain.features)
            except UnicodeDecodeError:
                subcat_full_derivation_bracketing += "("+STRING+"##"+expression.sc+"##"+"##".join(expression.head_chain.features)
            subcat_full_derivation_bracketing = appendMovingChains(expression, subcat_full_derivation_bracketing)
        except Exception as e:
            STRING = "##".join(["##".join(YIELD.get_string().encode('utf8').split(" "))+"@COMMA@" for part in expression.head_chain.string.narrow_yield.get_string() for YIELD in part if expression.head_chain.string.narrow_yield.get_string() != 't'])
            if STRING == '\xce\xb5':
                STRING = ""
            #chop off the final comma
            STRING = re.sub("@COMMA@$", "", STRING, count=10000)
            STRING = re.sub("##$", "", STRING, count=10000)
            STRING = re.sub("@COMMA@$", "", STRING, count=10000)
            STRING = re.sub("^@COMMA@##", "", STRING, count=10000)
            STRING = re.sub("@COMMA@##:", "##:", STRING, count=10000)
            STRING = re.sub("##@COMMA@", "", STRING, count=10000)
            STRING = re.sub("@COMMA@##:", "##:", STRING, count=10000)
            if STRING == "":
                STRING = '\xce\xb5'
            try:
                subcat_full_derivation_bracketing += "("+STRING.encode('utf8')+"##"+expression.sc+"##"+"##".join(expression.head_chain.features)
            except UnicodeDecodeError:
                subcat_full_derivation_bracketing += "("+STRING+"##"+expression.sc+"##"+"##".join(expression.head_chain.features)
            subcat_full_derivation_bracketing = appendMovingChains(expression, subcat_full_derivation_bracketing)
    elif expression.sc == ":\u0305":
        try:
            STRING = "##".join(expression.head_chain.string.narrow_yield.get_string().encode('utf8').split(" "))
            if STRING == '\xce\xb5':
                STRING = ""
            STRING = re.sub("@COMMA@$", "", STRING, count=10000)
            if STRING == '\xce\xb5':
                STRING = ""
            STRING = "##".join(expression.head_chain.string.narrow_yield.get_string().split(" "))
            STRING = re.sub("##$", "", STRING, count=10000)
            STRING = re.sub("@COMMA@$", "", STRING, count=10000)
            STRING = re.sub("^@COMMA@##", "", STRING, count=10000)
            STRING = re.sub("@COMMA@##:", "##:", STRING, count=10000)
            STRING = re.sub("##@COMMA@", "", STRING, count=10000)
            STRING = re.sub("@COMMA@##:", "##:", STRING, count=10000)
            if STRING == "":
                STRING = '\xce\xb5'
            try:
                subcat_full_derivation_bracketing += "("+STRING.encode('utf8')+"##:\u0305##"+"##".join(expression.head_chain.features)
            except UnicodeDecodeError:
                subcat_full_derivation_bracketing += "("+STRING+"##:\u0305##"+"##".join(expression.head_chain.features)
            subcat_full_derivation_bracketing = appendMovingChains(expression, subcat_full_derivation_bracketing)
        except Exception as e:
            STRING = "##".join(["##".join(YIELD.get_string().split(" "))+"@COMMA@" for part in expression.head_chain.string.narrow_yield.get_string() for YIELD in part if expression.head_chain.string.narrow_yield.get_string() != 't']).encode('utf8')
            S2 = copy.deepcopy(STRING)
            if STRING == '\xce\xb5':
                STRING = ""
            STRING = re.sub("@COMMA@$", "", STRING, count=10000)
            STRING = re.sub("##$", "", STRING, count=10000)
            STRING = re.sub("@COMMA@$", "", STRING, count=10000)
            STRING = re.sub("^@COMMA@##", "", STRING, count=10000)
            STRING = re.sub("##@COMMA@", "", STRING, count=10000)
            STRING = re.sub("@COMMA@##:", "##:", STRING, count=10000)
            if STRING == "":
                STRING = '\xce\xb5'
            try:
                subcat_full_derivation_bracketing += "("+STRING.encode('utf8')+"##:\u0305##"+"##".join(expression.head_chain.features)
            except Exception as e:
                subcat_full_derivation_bracketing += "("+STRING+"##:\u0305##"+"##".join(expression.head_chain.features)
            subcat_full_derivation_bracketing = appendMovingChains(expression, subcat_full_derivation_bracketing)
    if expression.pointers[0][0]['operation'] == 'type_saturation':
        subcat_derivation_bracketing += "(type_sat "
        (subcat_derivation_bracketing, subcat_full_derivation_bracketing) = generate_derivation_bracketing(expression.pointers[0][1], subcat_derivation_bracketing, subcat_full_derivation_bracketing)
        subcat_derivation_bracketing += ")"
        subcat_full_derivation_bracketing += ")"
    elif expression.pointers[0][0]['operation'] == 'merge':
        if expression.pointers[0][0]['phonetic_merge'] == True:
            p = "_phon"
        else:
            p = ""
        if expression.pointers[0][0]['escape'] == True:
            edge = "_edge"
        else:
            edge = ""
        if expression.pointers[0][0]['adjoin'] == False:
            if expression.pointers[0][0]['hm_dir'] == 'left':
                if expression.pointers[0][0]['direction'] == 'left':
                    subcat_derivation_bracketing += "(l_merge_lhm"+p+edge
                else:
                    subcat_derivation_bracketing += "(r_merge_lhm"+p+edge
            elif expression.pointers[0][0]['hm_dir'] == 'right':
                if expression.pointers[0][0]['direction'] == 'left':
                    subcat_derivation_bracketing += "(l_merge_rhm"+p+edge
                else:
                    subcat_derivation_bracketing += "(r_merge_rhm"+p+edge
            elif expression.pointers[0][0]['hm_dir'] == 'excorp':
                if expression.pointers[0][0]['direction'] == 'left':
                    subcat_derivation_bracketing += "(l_merge_xhm"+p+edge
                else:
                    subcat_derivation_bracketing += "(r_merge_xhm"+p+edge
            elif expression.pointers[0][0]['hm_dir'] == 'atb':
                if expression.pointers[0][0]['direction'] == 'left':
                    subcat_derivation_bracketing += "(l_merge_hatb"+p+edge
                else:
                    subcat_derivation_bracketing += "(r_merge_hatb"+p+edge
            else:
                if expression.pointers[0][0]['direction'] == 'left':
                    subcat_derivation_bracketing += "(l_merge"+p+edge
                else:
                    subcat_derivation_bracketing += "(r_merge"+p+edge
                if expression.pointers[0][0]['lex_head_coord']:
                    subcat_derivation_bracketing += '_lex'
        else:
            if expression.pointers[0][0]['direction'] == 'left':
                subcat_derivation_bracketing += "(r_adjoin"+p+edge
            else:
                subcat_derivation_bracketing += "(l_adjoin"+p+edge
        blank = None
        if expression.pointers[0][0]['persist_selector'] == True:
            subcat_derivation_bracketing += "_ps "
            blank = True
        if expression.pointers[0][0]['persist_selectee'] == True:
            subcat_derivation_bracketing += "_sc "
            blank = True
        if expression.pointers[0][0]['ATB_drop'] == True:
            subcat_derivation_bracketing += "_atb "
            blank = True
        if expression.pointers[0][0]['split'] == True:
            subcat_derivation_bracketing += "_split "
            blank = True
        if blank == None:
            subcat_derivation_bracketing += " "
        for EXPRESSION in expression.pointers[0][1:]:
            (subcat_derivation_bracketing, subcat_full_derivation_bracketing) = generate_derivation_bracketing(EXPRESSION, subcat_derivation_bracketing, subcat_full_derivation_bracketing)
        subcat_derivation_bracketing += ")"
        subcat_full_derivation_bracketing += ")"
    elif expression.pointers[0][0]['operation'] == 'move':
        if expression.pointers[0][0]['covert'] == True:#1234
            subcat_derivation_bracketing += "(c_move"
        elif expression.pointers[0][0]['direction'] == 'right':
            subcat_derivation_bracketing += "(r_move"
        else:
            if expression.pointers[0][0]['phonetic_merge'] == True:
                p = "_phon"
            else:
                p = ""
            subcat_derivation_bracketing += "(l_move"+p
        if expression.pointers[0][0]['sc'] == True:
            subcat_derivation_bracketing += "_sc "
        else:
            subcat_derivation_bracketing += " "
        (subcat_derivation_bracketing, subcat_full_derivation_bracketing) = generate_derivation_bracketing(expression.pointers[0][1], subcat_derivation_bracketing, subcat_full_derivation_bracketing)
        subcat_derivation_bracketing += ")"
        subcat_full_derivation_bracketing += ")"
    elif expression.pointers[0][0]['operation'] == 'fcide':
        subcat_derivation_bracketing += "(fcide "
        (subcat_derivation_bracketing, subcat_full_derivation_bracketing) = generate_derivation_bracketing(expression.pointers[0][1], subcat_derivation_bracketing, subcat_full_derivation_bracketing)
        subcat_derivation_bracketing += ")"
        subcat_full_derivation_bracketing += ")"
    #we now need to strip off the subcat features from the expressions head chain
    #or this causes problems (since only copies of the expressions pointed to by the
    #pointers of this expression had subcat features put onto them, these can be left alone).
    i = -1
    for feature in expression.head_chain.features:
        i+=1
        stripped_feature = re.sub('{.*?}', '', feature)
        expression.head_chain.features[i] = stripped_feature
    return (subcat_derivation_bracketing, subcat_full_derivation_bracketing)

def appendMovingChains(expression, subcat_full_derivation_bracketing):
    for chain in expression.non_head_chains:
        STRING = "##".join(chain.string.narrow_yield.get_string().encode('utf8').split(" "))
        if STRING == '\xce\xb5':
            STRING = ""
        STRING = re.sub("##$", "", STRING, count=10000)
        STRING = re.sub("@COMMA@$", "", STRING, count=10000)
        STRING = re.sub("^@COMMA@##", "", STRING, count=10000)
        STRING = re.sub("##@COMMA@", "", STRING, count=10000)
        STRING = re.sub("@COMMA@##:", "##:", STRING, count=10000)
        if STRING == "":
            STRING = '\xce\xb5'
        full_features = get_full_features(chain)
        f_index = -1
        try:
            subcat_full_derivation_bracketing += ",##"+STRING.encode('utf8')+"##"+chain.sc+"##"+"##".join(full_features)
        except UnicodeDecodeError:
            subcat_full_derivation_bracketing += ",##"+STRING+"##"+chain.sc+"##"+"##".join(full_features)
    return subcat_full_derivation_bracketing

def addSubCatFeatures(expression):
    #we keep the selectional features (FIN, ACC, NOM, PERF etc) separate from the
    #actual selectors/selectees and licensors/licensees during parsing but then when we
    #build the bracketings we want to add everything back in..this function does that..
    f_index = -1
    full_features = []
    for feature in expression.head_chain.features:
        f_index+=1
        expression.head_chain.subcatAgreeFeatures[f_index].sort()
        if "{" in feature:
            #because these are the axiom expressions in the chart, we only need to add the brackets
            #once..
            full_feature = feature
        elif len(expression.head_chain.subcatAgreeFeatures[f_index]) > 0:
            #we need to insert the subcat features after the cat feature, e.g. d, and before any following
            #diacritic, e.g. =
            index = -1
            foundStart = False
            full_feature = feature
            for char in feature:
                index+=1
                if char not in ['\xe2', '=', '+', '-', '~', '≈', '^', '&', '?', '!', '>', '<']:
                    foundStart = True
                elif foundStart == True:
                    featureSuffix = feature[index:]
                    full_feature = feature[0:index]+"{"+".".join([f for f in expression.head_chain.subcatAgreeFeatures[f_index]])+"}"+featureSuffix
                    break
            #in case there was no feature suffix we do the following
            if'{' not in full_feature:
                full_feature = feature+"{"+".".join([f for f in expression.head_chain.subcatAgreeFeatures[f_index]])+"}"
        else:
            full_feature = feature
        full_features.append(full_feature)
    expression.head_chain.features = full_features
        
def check_goal(item,agenda,sentence_length,allowMoreGoals):
    if len(item.non_head_chains) > 0:
        return False
    if len(item.head_chain.features) == 0:
        return False
    #for c goals, we will enforce that they can only have a single feature left..
    if item.head_chain.features[0] in ['c', 'C']:
        if len(item.head_chain.features) > 1:
            return False
    for feature in item.head_chain.features:
        #if we are allowing non-c goals we still want to rule out any items with licensors
        #as these could never be checked even if the fragment had been merged with more structure
        #as we disallow goals containing moving chains (fragments don't feature elements in their
        #base (unmoved) positions)
        if '+' in feature:
            return False
    #we disallow subjunctive root clauses, otherwise we get two analyses for "Jack and Sue like Pete" owing to the base form of the verb
    if 'SUB' in item.head_chain.subcatAgreeFeatures[0]:
        return False
    fused_string = ""
    position = None
    item_start = 10000
    item_end = -1
    epsilon_found = False
    for part in item.head_chain.string.narrow_yield.get_string():
        if len(part) > 0:
            s = part[0].get_string()
            if s== u'\u03b5':
                epsilon_found = True
                continue
            if s != '' and part[0].get_span() != [[], []]:
                fused_string += s+" "
                part_start = part[0].get_span()[0]
                part_end = part[0].get_span()[1]
                if position ==  None:
                    #the first time around we do not need to do the position check as their is nothing
                    #preceding the first part
                    x=0
                else:
                    if position != part_start:
                        return False
                position = part_end
                if part_start < item_start:
                    item_start = part_start
                if part_end > item_end:
                    item_end = part_end
            elif s != '':
                fused_string += s+" "
    if fused_string == "":
        fused_string = u'\u03b5'
    if item_start != 0 or item_end != sentence_length:
        return False
    if len(fused_string) > 0:
        fused_string = fused_string[:-1]
    goal_item = copy_expression(item)
    goal_item.pointers = item.pointers
    goal_item.head_chain.string.narrow_yield.set_yield(fused_string, [item_start, item_end])
    chart[0][-1]['goal'].append(goal_item)
    if allowMoreGoals or (goal_item.head_chain.features[0] in ['c', 'C'] and 'MAIN' in goal_item.head_chain.subcatAgreeFeatures[0]):
        return True
                              
def fuse_dependents(l_dependent_yields, r_dependent_yields, check_dir = None, mother = None):
    #fuses all elements in a given part (left dependents or right dependents) performing some adjacency checks too, and eliminating epsilon symbols of empty strings
    #first a quick check to make sure that left dependent spans are indeed to the left of right (only need
    #to check last and first elements respectively as checks below will take care of order problems within each dependent list)
    rightmost_l_yield = None
    leftmost_r_yield = None
    for y in l_dependent_yields:
        if y.get_span() != [[], []]:
            rightmost_l_yield = y
    for y in r_dependent_yields:
        if y.get_span() != [[], []]:
            leftmost_r_yield = y
            break
    if rightmost_l_yield != None and leftmost_r_yield != None:
        if not rightmost_l_yield.get_span()[1] <= leftmost_r_yield.get_span()[0]:
            return False
    if check_dir == 'left':
        dependent_yields = l_dependent_yields
    elif check_dir == 'right':
        dependent_yields = r_dependent_yields
    if len(dependent_yields) > 1:
        yields_to_remove = []
        for y in dependent_yields:
            if y.get_string() == u'\u03b5':
                yields_to_remove.append(y)
        for y in yields_to_remove:
            if len(dependent_yields) > 1:
                dependent_yields.remove(y)
    new_yield = None
    if len(dependent_yields) > 1:
        span_1 = dependent_yields[0].get_span()
        span_2 = dependent_yields[1].get_span()
        string_1 = dependent_yields[0].get_string()
        string_2 = dependent_yields[1].get_string()          
        if string_1 != "":
            if string_2 != "":
                fused_string = string_1+" "+string_2
            else:
                fused_string = string_1
        elif string_2 != "":
            fused_string = string_2
        else:
            fused_string = ""
    if len(dependent_yields) == 1:
        new_yield = dependent_yields[0]
    elif span_2 == [[], []]:
        new_yield = Yield(fused_string, span_1)
    elif span_1 == [[], []]:
        new_yield = Yield(fused_string, span_2)
    else:
        if span_1[1] == span_2[0]:
            new_yield = Yield(fused_string, [span_1[0], span_2[1]])
    if new_yield != None:
        if check_dir == 'left':
            del(mother.head_chain.string.l_dependent_yields[:])
            mother.head_chain.string.l_dependent_yields.append(new_yield)
        elif check_dir == 'right':
            del(mother.head_chain.string.r_dependent_yields[:])
            mother.head_chain.string.r_dependent_yields.append(new_yield)
        return True
    return False

def move(trigger_item, agenda, direction, resultsExpressionList=None, failure_messages=None, CONTINUE=[False], printPartialAnalyses=False):
    trigger_item_copy = copy_expression(trigger_item)
    trigger_item_copy_w_covert_mover = None
    #takes as input a constituent with a movement trigger and performs the movement..  we still need
    #a copy of the item to point to for the parser
    #we lower case everything because move applies whatever the case of the licensee and licensor features.
    #capitals on licensor indicate overt movement, lowercase indicate covert movement; capitals on the licensee
    #indicate persistent features, lowercase indicate non-persistent features (all features persist when selected by X≈)
    target_cat = cat_pattern.search(trigger_item_copy.head_chain.features[0]).group(0).lower()
    #rightward movement is to an adjoined position, hence it is treated here as scrambling and handled
    #as in Frey and Gartner 2002
    if "?" in trigger_item_copy.head_chain.features[0] or "!" in trigger_item_copy.head_chain.features[0]:
        #suicidal features are those which trigger intermediate (ie successive cyclic) A'-movement.. they have the following properties:
        #1. they are licensor features; 2. they can attract licensee features, but if there are no licensee features to attract, they self destruct, ie check themselves;
        #3. the ? versions fail to check (ie delete) the licensee features that they attract, whereas the ! versions do check those features.
        suicidal_feature = True
        if "!" in trigger_item_copy.head_chain.features[0]:
            suicidal_checker = True
        else:
            suicidal_checker = False
    else:
        suicidal_feature = False
        suicidal_checker = False
    match_count = 0
    matching_chain = None
    #find the chain with the matching licensee
    for chain in trigger_item_copy.non_head_chains:
        if direction == 'right' and "~" not in chain.features[0]:
            continue
        stripped_feature = chain.features[0].strip("-")
        stripped_feature = stripped_feature.strip("~")
        if stripped_feature.lower() == target_cat:
            matching_chain = chain
            CONTINUE[0] = True
            break
    if matching_chain == None:
        if suicidal_feature == False:
            if resultsExpressionList != None:
                failure_messages.append("Probing for matching licensee goal failed.")
            return
        else:
            #if the trigger was a suicidal feature, it does not need to attract anything, and if there is nothing to check against, it simply self destructs - ie checks itself
            trigger_item_copy.head_chain.checked_features.append(trigger_item_copy.head_chain.features[0])
            del(trigger_item_copy.head_chain.features[0])
            del(trigger_item_copy.head_chain.subcatAgreeFeatures[0])
            trigger_item_copy.pointers.append(({'operation':'fcide'}, trigger_item))
            if resultsExpressionList == None:
                add_to_agenda(trigger_item_copy, agenda, move_arg=trigger_item, printPartialAnalyses=printPartialAnalyses)
            else:
                resultsExpressionList.append(trigger_item_copy)
            return
    original_matching_chain_features = copy.deepcopy(matching_chain.features)
    #placing a ban on rightward movement of empty constituents to improve efficiency..
    #given that rightward movement is pf operation, even moving PRO rightwards should be impossible
    if direction == 'right' and matching_chain.string.narrow_yield.get_span() == [[], []]:
        if resultsExpressionList != None:
            failure_messages.append("Rightward movement of empty constituents is disallowed.")
        return
    #now we check that the fine-grained selectional requirements of the selector are met..
    variable_found = False
    if direction == 'right':
        requirer = matching_chain
        required = trigger_item_copy.head_chain
    else:
        requirer = trigger_item_copy.head_chain
        required = matching_chain
    if requirer.subcatAgreeFeatures[0] != []:
        for subcatAgreeFeature in requirer.subcatAgreeFeatures[0]:
            if subcatAgreeFeature in sel_variables:
                variable_found = True
                variable = subcatAgreeFeature
            else:
                fork = re.search('\[.*?\|.*?\]', subcatAgreeFeature)
                if fork:
                    options = fork.group(0)[1:-1].split("|")
                ignore_subcats = False
                reified_case_feature = False
                if len(required.checked_features) > 0:
                    #to handle that-trace and anti-that-trace effects, we will assume that when a DP is sat in its case position,
                    #only its actual case-valuation is visible to the selector, hence any other case subcat features it
                    #bears will not be taken into consideration - only while it is in this position.. as soon
                    #as it moves they become visible again, just as they do for atb movement out of embedded clauses
                    if len(required.checked_features[-1]) > 1:
                        if required.checked_features[-1][1:] in case_features:
                            reified_case_feature = required.checked_features[-1][1:]
                if '+' == subcatAgreeFeature[0]:
                    match_found = False
                    if fork:
                        #we allow the user to specify that a selectee
                        #can have one of a number of options.  This allows us to to say, e.g., that a prepositional
                        #object can be either GEN or ACC (but must not be NOM).
                        for sf in options:
                            if reified_case_feature and sf in case_features:
                                if sf == reified_case_feature:
                                    match_found = True
                                    break
                                else:
                                    #doesn't matter whether the correct subcat is in the licensee's subcats now, as we know the true case of this DP
                                    if resultsExpressionList != None:
                                        failure_messages.append("Failure of absolute case-matching ("+reified_case_feature+") requirements.")
                                    return
                            elif sf in required.subcatAgreeFeatures[0]:
                                match_found = True
                                break
                    else:
                        if reified_case_feature and subcatAgreeFeature[1:] in case_features:
                            if subcatAgreeFeature[1:] == reified_case_feature:
                                match_found = True
                            else:
                                if resultsExpressionList != None:
                                    failure_messages.append("Failure of absolute case-matching ("+reified_case_feature+") requirements.")
                                return
                    if not match_found and subcatAgreeFeature[1:] not in required.subcatAgreeFeatures[0]:
                        if resultsExpressionList != None:
                            failure_messages.append("c-selectional (subcategorization) or agreement requirements not met.")
                        return
                elif '-' == subcatAgreeFeature[0]:
                    match_found = True
                    if fork:
                        #we allow the user to specify that a selectee
                        #can have one of a number of options.  This allows us to to say, e.g., that a prepositional
                        #object can be either GEN or ACC (but must not be NOM).
                        for sf in options:
                            if reified_case_feature and sf in case_features:#1234
                                if sf != reified_case_feature:
                                    #now that we have established the true case of this DP, we can ignore its subcat features and just abort this derivation
                                    if resultsExpressionList != None:
                                        failure_messages.append("Failure of absolute case-matching ("+reified_case_feature+") requirements.")
                                    match_found = False
                                    ignore_subcats = True
                                    break
                            elif sf not in required.subcatAgreeFeatures[0]:
                                match_found = False
                                break
                            elif sf in required.subcatAgreeFeatures[0]:
                                #if the subcat feature is part of a paradigm then we may have a case of
                                #syncretism, in which case we do not want -NOM to abort the derivation just because
                                #the mover has a NOM feature IFF it also has an ACC or GEN feature etc.. same for phi features
                                paradigm = None
                                for p in paradigms:
                                    if sf in p:
                                        paradigm = p
                                        break
                                if paradigm != None:
                                    BREAK = False
                                    for f in required.subcatAgreeFeatures[0]:
                                        if f != sf and f in paradigm:
                                            match_found = False
                                            BREAK = True
                                            break
                                    if BREAK:
                                        break
                    else:
                        if reified_case_feature and reified_case_feature == subcatAgreeFeature[1:]:
                            if resultsExpressionList != None:
                                failure_messages.append("Failure of absolute case-matching ("+reified_case_feature+") requirements.")
                            #subcat features are irrelevant now, as we know the true case of this DP
                            return
                        elif subcatAgreeFeature[1:] not in required.subcatAgreeFeatures[0]:
                            match_found = False
                        elif subcatAgreeFeature[1:] in required.subcatAgreeFeatures[0]:
                            paradigm = None
                            for p in paradigms:
                                if subcatAgreeFeature[1:] in p:
                                    paradigm = p
                                    break
                            if paradigm != None:
                                for f in required.subcatAgreeFeatures[0]:
                                    if f != subcatAgreeFeature[1:] and f in paradigm and '-'+f not in requirer.subcatAgreeFeatures[0]:
                                        match_found = False
                                        break
                    if match_found:
                        if resultsExpressionList != None:
                            failure_messages.append("c-selectional (subcategorization) or agreement requirements not met.")
                        return
                elif '~' == subcatAgreeFeature[0]:
                    if subcatAgreeFeature[1:] in required.subcatAgreeFeatures[0]:
                        required.subcatAgreeFeatures[0].remove(subcatAgreeFeature[1:])
                else:
                    if fork:
                        abort = True
                        #the case where the +/- is not outside the OR brackets
                        for sf in options:
                            if sf[0] == "+":
                                if reified_case_feature and sf[1:] in case_features:
                                    if sf[1:] == reified_case_feature:
                                        abort = False
                                        break
                                    else:
                                        if resultsExpressionList != None:
                                            failure_messages.append("Failure of absolute case-matching ("+reified_case_feature+") requirements.")
                                        return
                                elif sf[1:] in required.subcatAgreeFeatures[0]:
                                    abort = False
                                    break
                            elif sf[0] == "-":
                                if reified_case_feature and sf[1:] in case_features:
                                    if reified_case_feature != sf[1:]:
                                        abort = False
                                        break
                                elif sf[1:] not in required.subcatAgreeFeatures[0]:
                                    abort = False
                                    break
                                elif sf[1:] in required.subcatAgreeFeatures[0]:
                                    paradigm = None
                                    for p in paradigms:
                                        if sf[1:] in p:
                                            paradigm = p
                                            break
                                    if paradigm != None:
                                        for f in required.subcatAgreeFeatures[0]:
                                            if f != sf[1:] and f in paradigm:
                                                abort = False
                                                break
                        if abort:
                            if resultsExpressionList != None:
                                failure_messages.append("c-selectional (subcategorization) or agreement requirements not met.")
                            return
    if variable_found == True and direction != 'right':
        #if a variable was found in the licensor's first set of property/requirement features, then the
        #licensee's property features must replace this variable in all other sets of selectional features on the licensor
        #which also have this variable...this corresponds to simply passing e.g. the lexical verbs PAST feature onto
        #little v..
        #if the selectee's feature is -num or -pers then we split the +3SG, +2PL etc agreement features up into e.g. +3 and +PL
        j=-1
        for subcatAgreeFeatures in trigger_item_copy.head_chain.subcatAgreeFeatures:
            j+=1
            for f in subcatAgreeFeatures:
                if variable == f:
                    for subcatAgreeFeature in matching_chain.subcatAgreeFeatures[0]:
                        if subcatAgreeFeature not in sel_variables and subcatAgreeFeature not in subcatAgreeFeatures and subcatAgreeFeature not in ['COORD', 'LH', 'EXCORP']:
                            subcatAgreeFeatures.append(subcatAgreeFeature)
            subcatAgreeFeatures.sort()
        for item in trigger_item_copy.head_chain.subcatAgreeFeatures:
            if variable in item:
                item.remove(variable)
    #if the mover is covert, we must check that the movement trigger is weak..This is different to the
    #similar checks below which look to see if the ONWARD movement of an overtly moved element will be covert..
    if matching_chain.covert:
        if trigger_item.head_chain.features[0].isupper():# and "?" not in trigger_item.head_chain.features[0]:#I removed this last clause on 1st April 2017 as we want to allow suicidal features to be overt vs covert movement triggers
            if resultsExpressionList != None:
                failure_messages.append("Non-onward moving covert movement to overt movement licensor attempted.")
            return
    elif not (suicidal_feature and not suicidal_checker) and not matching_chain.covert and trigger_item.head_chain.features[0].islower() and (len(matching_chain.features) == 1 or re.search('\w+~', matching_chain.features[1])) and '+' in trigger_item.head_chain.features[0]:
        #by the same token, if the mover is overt and the licensor is a covert movement trigger,
        #unless the licensee is moving onwards (as with wh-movement following case checking, or after checking a ? sucidal licensor), we abort.. (this does not apply where the movement 'trigger' is
        #just a category, as with rightward movement, since this is always overt..also, if the next movement licensee feature is
        #a rightward movement feature, this does not license overt movement here, since we want the phonetic features to
        #remain in the current position until they move later (as this is PF movement).
        if resultsExpressionList != None:
            failure_messages.append("Overt movement to covert movement licensor (without onward movement) attepted.")
        return
    if direction == 'left' and not (suicidal_feature and not suicidal_checker) and not matching_chain.covert and trigger_item.head_chain.features[0].islower():
        matching_chain.overt_movement_required = True
    elif trigger_item.head_chain.features[0].isupper():
        matching_chain.overt_movement_required = False
    #first we will make copies of the left and right dependent yields as we will need them
    #later if we have the potential for successive cyclic movement..
    l_dependent_yield_copy = copy.deepcopy(trigger_item_copy.head_chain.string.l_dependent_yields)
    r_dependent_yield_copy = copy.deepcopy(trigger_item_copy.head_chain.string.r_dependent_yields)
    narrow_yield_copy = copy.deepcopy(trigger_item_copy.head_chain.string.narrow_yield)
    #now check to see whether the moving item will move again..
    if len(matching_chain.features) == 1 and ((not suicidal_feature) or suicidal_checker):
        if matching_chain.overt_movement_required:
            if resultsExpressionList != None:
                failure_messages.append("Earlier overt-to-covert-licensor movement without subsequent overt movement detected.")
            return
        #ie is not moving further..
        trigger_item_copy.head_chain.inside_cost += matching_chain.inside_cost
        #just as with merge, we need to check the order of any existing complement relative to the
        #head and preserve this order..  We also again assume here that each phrase can only have at most 1 overt spec
        matching_chain_span = matching_chain.string.narrow_yield.get_span()
        trigger_item_copy_span = trigger_item_copy.head_chain.string.narrow_yield.get_span()
        if direction == 'left':
            #leftward movement to spec position
            if trigger_item_copy_span != [[], []] and matching_chain_span != [[], []]:
                new_span = [matching_chain_span[0], trigger_item_copy_span[1]]
            elif matching_chain_span != [[], []]:
                new_span = matching_chain_span
            elif trigger_item_copy_span != [[], []]:
                new_span = trigger_item_copy_span
            else:
                new_span = [[], []]
            trigger_item_copy.head_chain.string.l_dependent_yields.insert(0, matching_chain.string.narrow_yield)
            if fuse_dependents(trigger_item_copy.head_chain.string.l_dependent_yields, trigger_item_copy.head_chain.string.r_dependent_yields, check_dir = 'left', mother = trigger_item_copy) == False:
                if resultsExpressionList != None:
                    failure_messages.append("String adjacency checks for attempted final movement failed.")
                return
            trigger_item_copy.head_chain.string.narrow_yield.set_span(new_span)
            #delete licensor feature after adding it to trigger_item_copy's checked_features list
            trigger_item_copy.head_chain.checked_features.append(trigger_item_copy.head_chain.features[0])
            del(trigger_item_copy.head_chain.features[0])
            del(trigger_item_copy.head_chain.subcatAgreeFeatures[0])
        elif direction == 'right':
            #rightward movement/extraposition (as scrambling) to right adjoined position..
            if trigger_item_copy_span[1] != []:
                new_span = [trigger_item_copy_span[0], matching_chain_span[1]]
            else:
                new_span = [matching_chain_span[0], matching_chain_span[1]]
            trigger_item_copy.head_chain.string.r_dependent_yields.append(matching_chain.string.narrow_yield)
            if fuse_dependents(trigger_item_copy.head_chain.string.l_dependent_yields, trigger_item_copy.head_chain.string.r_dependent_yields, check_dir = 'right', mother = trigger_item_copy) == False:
                if resultsExpressionList != None:
                    failure_messages.append("String adjacency checks for attempted rightward movement failed.")
                return
            trigger_item_copy.head_chain.string.narrow_yield.set_span(new_span)
            trigger_item_copy.head_chain.string.narrow_yield.string[2] = [trigger_item_copy.head_chain.string.r_dependent_yields[0]]
    else:
        #ie it is moving further..
        if covert_move_on == True and not (len(matching_chain.features) > 1 and re.search('\w+~', matching_chain.features[1])):
            #we cannot have covert rightward movement, since rightward movement is PF operation..
            #we only want to bother generating a version of the expression with covert movement if the chain
            #has some overt yield..otherwise it is already covert! (since other null elements, eg. null heads, do not move on their own I assume)
            if matching_chain.string.narrow_yield.get_span() == [[], []]:
                trigger_item_copy_w_covert_mover = None
            else:
                pf_chain = None
                trigger_item_copy_w_covert_mover = copy_expression(trigger_item_copy)
                trigger_item_copy_w_covert_mover.head_chain.inside_cost += matching_chain.inside_cost
                #now need to find the matching chain within the expression with the covert mover
                for chain in trigger_item_copy_w_covert_mover.non_head_chains:
                    stripped_feature = chain.features[0].strip("-")
                    if stripped_feature.lower() == target_cat:
                        covert_matching_chain = chain
                        chain.covert = True
                        break
                #keep the string and span of this chain to one side before clearing it, so we can insert it
                #into the current projection's spec (or keep it in a separate chain if there'll be
                #subsequent rightward movement)..  this is for the case where something first moves overtly, then
                #from this position it moves covertly..
                covert_chain_string = covert_matching_chain.string.narrow_yield.get_string()
                covert_chain_span = covert_matching_chain.string.narrow_yield.get_span()
                covert_matching_chain.string.narrow_yield.set_yield("", [[], []])
                #if the matching chain has a x~ feature then we create a new PF chain housing just this feature and the string/span info
                #and delete the wt feature from the covert LF chain..This is because, if an object moves covertly to check case
                #and then subsequently it is shifted to the right, it should shift from the position it was in immediately prior to the
                #covert movement, not from the covert movement landing site since the phonetic features never moved to this location.
                #of course, the matching chain must have at least two movement features behind the one being checked here (leftward and rightward) to make
                #this necessary, otherwise it is already essentially just a PF chain after the current feature is checked..
                if len(covert_matching_chain.features) > 2:
                    for i in range(len(covert_matching_chain.features)):
                        if re.search('\w+~', covert_matching_chain.features[i]):
                            r_move_feature = re.search('\w+~', covert_matching_chain.features[i]).group(0)
                            r_move_subcatAgreeFeatures = covert_matching_chain.subcatAgreeFeatures[i]
                            del(covert_matching_chain.features[i])
                            del(covert_matching_chain.subcatAgreeFeatures[i])
                            pf_chain = copy_chain(covert_matching_chain)
                            pf_chain.covert = False
                            pf_chain.features = [r_move_feature]
                            pf_chain.subcatAgreeFeatures = [r_move_subcatAgreeFeatures]
                            pf_chain.string.narrow_yield.set_string(covert_chain_string)
                            pf_chain.string.narrow_yield.set_span(covert_chain_span)
                            trigger_item_copy_w_covert_mover.non_head_chains.append(pf_chain)
                            break
        else:
            trigger_item_copy_w_covert_mover = None
        #it is moving..so we simply delete the licensor and licensee features (only licensee for rightward movement)
        if direction == 'left':
            trigger_item_copy.head_chain.checked_features.append(trigger_item_copy.head_chain.features[0])
            del(trigger_item_copy.head_chain.features[0])
            del(trigger_item_copy.head_chain.subcatAgreeFeatures[0])
            #we need to leave a trace in the spec position, or a full overt copy if covert movement.. if we have split the chain into
            #both pf and lf chains (for the case where there is both covert and pf movement) then we leave a trace and keep the pf chain separate.
            if trigger_item_copy_w_covert_mover != None:
                trigger_item_copy_w_covert_mover.head_chain.checked_features.append(trigger_item_copy_w_covert_mover.head_chain.features[0])
                del(trigger_item_copy_w_covert_mover.head_chain.features[0])
                del(trigger_item_copy_w_covert_mover.head_chain.subcatAgreeFeatures[0])
                if pf_chain == None:
                    trigger_item_copy_w_covert_mover.head_chain.string.l_dependent_yields.insert(0, Yield(covert_chain_string, covert_chain_span))
                if fuse_dependents(trigger_item_copy_w_covert_mover.head_chain.string.l_dependent_yields, trigger_item_copy_w_covert_mover.head_chain.string.r_dependent_yields, check_dir = 'left', mother = trigger_item_copy_w_covert_mover) == False:
                    if resultsExpressionList != None:
                        failure_messages.append("String adjacency checks for attempted movement failed.")
                    trigger_item_copy_w_covert_mover = None
                else:
                    (left_pos, right_pos) = find_narrow_yield(trigger_item_copy_w_covert_mover)
                    trigger_item_copy_w_covert_mover.head_chain.string.narrow_yield.set_span([left_pos, right_pos])
            if fuse_dependents(trigger_item_copy.head_chain.string.l_dependent_yields, trigger_item_copy.head_chain.string.r_dependent_yields, check_dir = 'left', mother = trigger_item_copy) == False:
                if resultsExpressionList != None:
                    failure_messages.append("String adjacency checks for attempted movement failed.")
                trigger_item_copy = None
            else:
                (left_pos, right_pos) = find_narrow_yield(trigger_item_copy)
                trigger_item_copy.head_chain.string.narrow_yield.set_span([left_pos, right_pos])
        else:
            #This code should never be executed as we should not have syntactic movement following PF movement..
            #covert movement not implemented here..since this is PF movement, move-F makes no sense here..
            if fuse_dependents(trigger_item_copy.head_chain.string.l_dependent_yields, trigger_item_copy.head_chain.string.r_dependent_yields, check_dir = 'right', mother = trigger_item_copy) == False:
                if resultsExpressionList != None:
                    failure_messages.append("String adjacency checks for attempted movement failed.")
                return
            (left_pos, right_pos) = find_narrow_yield(trigger_item_copy)
            trigger_item_copy.head_chain.string.narrow_yield.set_span([left_pos, right_pos])
    #As long as this trigger_item_copy still has one feature left in its head chain, it is still
    #useful and should be added back to the agenda.
    items_w_persist_mover = []
    for item in [trigger_item_copy_w_covert_mover, trigger_item_copy]:
        if item != None:
            if item == trigger_item_copy:
                mc = matching_chain
            else:
                mc = covert_matching_chain
            #if the licensee/selectee feature is strong (in capitals) then we must allow it to optionally
            #persist.. hence we create a second copy of the item and only delete the first feature of the chain in the
            #first item..
            lic = re.search('\w+', mc.features[0]).group(0)
            if lic in ['D']: #only D may persist
                item_w_persist_mover = copy_expression(item)
                if item == trigger_item_copy_w_covert_mover:
                    l_dependent_yield = item_w_persist_mover.head_chain.string.l_dependent_yields
                    r_dependent_yield = item_w_persist_mover.head_chain.string.r_dependent_yields
                else:
                    l_dependent_yield = l_dependent_yield_copy
                    r_dependent_yield = r_dependent_yield_copy
                if fuse_dependents(l_dependent_yield, r_dependent_yield, check_dir = direction, mother = item_w_persist_mover) == False:
                    item_w_persist_mover = None
                else:
                    if item != trigger_item_copy_w_covert_mover:
                        item.head_chain.string.narrow_yield = narrow_yield_copy
                        item.head_chain.string.narrow_yield.set_string([item.head_chain.string.l_dependent_yields, item.head_chain.string.head_yield, item.head_chain.string.r_dependent_yields])
                    (left_pos, right_pos) = find_narrow_yield(item_w_persist_mover)
                    item_w_persist_mover.head_chain.string.narrow_yield.set_span([left_pos, right_pos])
            else:
                item_w_persist_mover = None
            case_feature_just_valued = False
            if (not suicidal_feature) or suicidal_checker:
                mc.checked_features.append(mc.features[0])
                if mc.checked_features[-1] in ["-case", "-CASE"]:
                    #the following case feature valuations allow us to record some history of the derivation in the category type
                    #which allows us to rule out "he knows [who jack kissed and hit mary]"
                    if trigger_item_copy.cat_feature == "v":
                        mc.checked_features[-1] = "-ACC"
                        case_feature_just_valued = True
                    elif trigger_item_copy.cat_feature == "t":
                        mc.checked_features[-1] = "-NOM"
                        case_feature_just_valued = True
                    elif trigger_item_copy.cat_feature == "p":
                        mc.checked_features[-1] = "-DAT"
                        case_feature_just_valued = True
                    elif trigger_item_copy.cat_feature == "d":
                        mc.checked_features[-1] = "-GEN"
                        case_feature_just_valued = True
                del(mc.features[0])
                del(mc.subcatAgreeFeatures[0])
            index=-1
            if not case_feature_just_valued:
                if mc.checked_features[-1] in ['-ACC', '-NOM', '-DAT', '-GEN']:
                    mc.checked_features[-1] = '-CASE'
            if len(mc.features) == 0:
                #remove the matching chain from trigger_item_copy as its features are exhausted
                item.non_head_chains.remove(mc)
            if len(item.head_chain.features) > 0:
                #we only add this item to the agenda if it still has at least one feature left
                item.non_head_chains = sorted(item.non_head_chains, key=lambda x: x.string.narrow_yield.span)
                if item_w_persist_mover != None:
                    item_w_persist_mover.non_head_chains = sorted(item_w_persist_mover.non_head_chains, key=lambda x: x.string.narrow_yield.span)
                    if item == trigger_item_copy_w_covert_mover:
                        item_w_persist_mover.pointers.append(({'operation':'move', 'phonetic_merge':True, 'direction':direction, 'covert':matching_chain.covert, 'sc':True}, trigger_item))
                    else:
                        item_w_persist_mover.pointers.append(({'operation':'move', 'phonetic_merge':False, 'direction':direction, 'covert':matching_chain.covert, 'sc':True}, trigger_item))
                if item == trigger_item_copy_w_covert_mover:
                    item.pointers.append(({'operation':'move', 'phonetic_merge':True, 'direction':direction, 'covert':matching_chain.covert, 'sc':False}, trigger_item))
                else:
                    item.pointers.append(({'operation':'move', 'phonetic_merge':False, 'direction':direction, 'covert':matching_chain.covert, 'sc':False}, trigger_item))
                len_original_matching_chain_features = len(original_matching_chain_features)
                found_overt_only_mover = False
                found_overt_only_mover_in_persistent = False
                found_covert_only_mover = False
                found_neutral_feature = False
                if item == trigger_item_copy_w_covert_mover:
                    if len(original_matching_chain_features) > 1 and (not (suicidal_feature and not suicidal_checker)):#i.e. the licensor is a checker
                        features_to_search = original_matching_chain_features[1:]
                    elif suicidal_feature and not suicidal_checker:#i.e. the licensor is not a checker, i.e. it will not delete the licensee feature
                        features_to_search = original_matching_chain_features[0:]
                    for feature in features_to_search:
                        if feature.lower() in overt_only_movers:
                            found_overt_only_mover = True
                            break
                    if found_overt_only_mover or original_matching_chain_features[0].lower() in overt_only_movers:
                        #persistent feature are only D which is an overt only mover, so no need to check this for covert_only
                        found_overt_only_mover_in_persistent = True
                if item != trigger_item_copy_w_covert_mover and matching_chain.string.narrow_yield.get_span() != [[],[]]:
                    features_to_search = None
                    if len(original_matching_chain_features) > 1 and (not (suicidal_feature and not suicidal_checker)):#i.e. the licensor is a checker
                        features_to_search = original_matching_chain_features[1:]
                    elif suicidal_feature and not suicidal_checker:#i.e. the licensor is not a checker, i.e. it will not delete the licensee feature
                        features_to_search = original_matching_chain_features[0:]
                    if features_to_search != None and features_to_search[0].lower() in covert_only_movers:
                        found_covert_only_mover = True
                if resultsExpressionList == None:
                    if item == trigger_item_copy_w_covert_mover:
                        #note that if the onward movement is covert but the movement to this position was overt, then we enforce that if the licensor is a ? non-checker, the licensee feature checked must be in phi features..
                        #This is to rule out cases where e.g. wh moves overtly to embedded spec CP and the covertly onwards.
                        if not found_overt_only_mover and (original_matching_chain_features[0].lower() in multiple_agree_features or matching_chain.covert or (not (suicidal_feature and not suicidal_checker))):###
                            add_to_agenda(item, agenda, move_arg=trigger_item, printPartialAnalyses=printPartialAnalyses)
                    elif not found_covert_only_mover and len_original_matching_chain_features > 1:
                        add_to_agenda(item, agenda, move_arg=trigger_item, printPartialAnalyses=printPartialAnalyses)
                    elif not found_covert_only_mover and len_original_matching_chain_features == 1:
                        add_to_agenda(item, agenda, move_arg=trigger_item, printPartialAnalyses=printPartialAnalyses)
                else:
                    if item == trigger_item_copy_w_covert_mover:
                        if not found_overt_only_mover and (original_matching_chain_features[0].lower() in multiple_agree_features or matching_chain.covert or (not (suicidal_feature and not suicidal_checker))):
                            resultsExpressionList.append(item)
                    elif not found_covert_only_mover and len_original_matching_chain_features > 1:
                        resultsExpressionList.append(item)
                    elif not found_covert_only_mover and len_original_matching_chain_features == 1:
                        resultsExpressionList.append(item)
                if item_w_persist_mover != None:
                    if resultsExpressionList == None:
                        if item == trigger_item_copy_w_covert_mover:
                            if not found_overt_only_mover_in_persistent:
                                add_to_agenda(item_w_persist_mover, agenda, move_arg=trigger_item, printPartialAnalyses=printPartialAnalyses)
                        else:
                            add_to_agenda(item_w_persist_mover, agenda, move_arg=trigger_item, printPartialAnalyses=printPartialAnalyses)
                    else:
                        if item == trigger_item_copy_w_covert_mover:
                            if not found_overt_only_mover_in_persistent:
                                resultsExpressionList.append(item_w_persist_mover)
                        else:
                            resultsExpressionList.append(item_w_persist_mover)

def merge(trigger_item, target_item, agenda, sentence_length, resultsExpressionList=None, failure_messages=None, adjoin_or_coord_only=False, ss=None, ms=None, printPartialAnalyses=False):
    global source_spans
    global moveable_spans
    if ss != None:
        source_spans = ss
    if ms != None:
        moveable_spans = ms
    #resultsExpressionList is relevant to the external autobank program..
    if trigger_item.head_chain.head_string in type_raisers:
        #for efficiency reasons, we do not allow type raising of categories already type raised.. this is a much more
        #general notion of type raising than in CCG..
        if target_item.head_chain.head_string in type_raisers:
            if resultsExpressionList != None:
                failure_messages.append("Attempted to merge type-raiser head with already type-raised constituent.")
            return
    if '=' in trigger_item.head_chain.features[0] or '≈' in trigger_item.head_chain.features[0]:
        if '=' in target_item.head_chain.features[0] or '≈' in target_item.head_chain.features[0]:
            #we should only get here if we are calling this function from autobank,
            #in which case we must prevent both arguments being selectors
            if resultsExpressionList != None:
                failure_messages.append("Merger of selector with selector attempted.")
            return
        selector = trigger_item
        selectee = target_item
    elif '=' in target_item.head_chain.features[0] or '≈' in target_item.head_chain.features[0]:
        selector = target_item
        selectee = trigger_item
    else:
        if resultsExpressionList != None:
            failure_messages.append("No selector detected for merge operation.")
        return
    #we need to ban cases where an adjunctizer without a checking +wh feature takes a -wh
    #complement, since otherwise this can lead to infinite recursion owing to atb drop for
    #pied-piping wh-questions..so only adjunctizers which can percolate the -wh feature via checking
    #can be allowed to select these complements
    adjunctizer = False
    pied_piping_features = []
    for feature in selector.head_chain.features:
        if "≈" in feature:
            adjunctizer = True
        #we also want to disallow two heads with the same pied piping feature structure being in
        #a head complement relation since this leads to spurious ambiguity.. the following is a hack
        #ruling out this case for prepostional heads only..
        elif "+" in feature:
            if "-"+feature[1:] in selector.head_chain.features:
                if "-"+feature[1:] in selectee.head_chain.features and "p" in selectee.head_chain.features:
                    if resultsExpressionList != None:
                        failure_messages.append("Recursive pied-piping is disallowed.")
                    return
    #to prevent infinite recursion, we need to check that extraposers aren't selecting phrases already
    #marked for extraposition
    if "~" in [feature[-1] for feature in selector.head_chain.features]:
        if "~" in [feature[-1] for feature in selectee.head_chain.features]:
            if resultsExpressionList != None:
                failure_messages.append("Double extraposition is disallowed.")
            return
    #here, the more specific reg ex searches must come first..
    if re.search(right_merge_left_h_move, selector.head_chain.features[0]):
        if adjoin_or_coord_only and selector.head_string != '[dat]' and selector.head_chain.sc not in [':\u0305:\u0305', ':\\u0305:\\u0305', ':\u0305', ':\\u0305']:
            return
        MERGE(selector = selector, selectee = selectee, agenda = agenda, sentence_length = sentence_length, direction = 'right', hm_dir = 'left', excorp = False, resultsExpressionList=resultsExpressionList, failure_messages=failure_messages, printPartialAnalyses=printPartialAnalyses)
    elif re.search(right_merge_right_h_move, selector.head_chain.features[0]):
        if adjoin_or_coord_only and selector.head_string != '[dat]' and selector.head_chain.sc not in [':\u0305:\u0305', ':\\u0305:\\u0305', ':\u0305', ':\\u0305']:
            return
        MERGE(selector = selector, selectee = selectee, agenda = agenda, sentence_length = sentence_length, direction = 'right', hm_dir = 'right', excorp = False, resultsExpressionList=resultsExpressionList, failure_messages=failure_messages, printPartialAnalyses=printPartialAnalyses)
    elif re.search(right_merge_x_h_move, selector.head_chain.features[0]):
        if adjoin_or_coord_only and selector.head_string != '[dat]' and selector.head_chain.sc not in [':\u0305:\u0305', ':\\u0305:\\u0305', ':\u0305', ':\\u0305']:
            return
        MERGE(selector = selector, selectee = selectee, agenda = agenda, sentence_length = sentence_length, direction = 'right', hm_dir = 'excorp', excorp = True, resultsExpressionList=resultsExpressionList, failure_messages=failure_messages, printPartialAnalyses=printPartialAnalyses)
    elif re.search(right_merge, selector.head_chain.features[0]):
        if adjoin_or_coord_only and selector.head_string != '[dat]' and selector.head_chain.sc not in [':\u0305:\u0305', ':\\u0305:\\u0305', ':\u0305', ':\\u0305']:
            return
        MERGE(selector = selector, selectee = selectee, agenda = agenda, sentence_length = sentence_length, direction = 'right', excorp = False, resultsExpressionList=resultsExpressionList, failure_messages=failure_messages, printPartialAnalyses=printPartialAnalyses)
    elif re.search(left_merge_left_h_move, selector.head_chain.features[0]):
        if adjoin_or_coord_only and selector.head_string != '[dat]' and selector.head_chain.sc not in [':\u0305:\u0305', ':\\u0305:\\u0305', ':\u0305', ':\\u0305']:
            return
        MERGE(selector = selector, selectee = selectee, agenda = agenda, sentence_length = sentence_length, direction = 'right', hm_dir = 'left', excorp = False, resultsExpressionList=resultsExpressionList, failure_messages=failure_messages, printPartialAnalyses=printPartialAnalyses)
    elif re.search(left_merge_right_h_move, selector.head_chain.features[0]):
        if adjoin_or_coord_only and selector.head_string != '[dat]' and selector.head_chain.sc not in [':\u0305:\u0305', ':\\u0305:\\u0305', ':\u0305', ':\\u0305']:
            return
        MERGE(selector = selector, selectee = selectee, agenda = agenda, sentence_length = sentence_length, direction = 'right', hm_dir = 'right', excorp = False, resultsExpressionList=resultsExpressionList, failure_messages=failure_messages, printPartialAnalyses=printPartialAnalyses)
    elif re.search(left_merge_x_h_move, selector.head_chain.features[0]):
        if adjoin_or_coord_only and selector.head_string != '[dat]' and selector.head_chain.sc not in [':\u0305:\u0305', ':\\u0305:\\u0305', ':\u0305', ':\\u0305']:
            return
        MERGE(selector = selector, selectee = selectee, agenda = agenda, sentence_length = sentence_length, direction = 'left', hm_dir = 'excorp', excorp = True, resultsExpressionList=resultsExpressionList, failure_messages=failure_messages, printPartialAnalyses=printPartialAnalyses)
    elif re.search(left_merge, selector.head_chain.features[0]):
        if adjoin_or_coord_only and selector.head_string != '[dat]' and selector.head_chain.sc not in [':\u0305:\u0305', ':\\u0305:\\u0305', ':\u0305', ':\\u0305']:
            return
        MERGE(selector = selector, selectee = selectee, agenda = agenda, sentence_length = sentence_length, direction = 'left', excorp = False, resultsExpressionList=resultsExpressionList, failure_messages=failure_messages, printPartialAnalyses=printPartialAnalyses)
    elif re.search(right_adjoin, selector.head_chain.features[0]):
        #even though this is called 'right adjoin' the selector is the adjunct itself, hence direction = left..conversely for 'left adjoin'
        MERGE(selector = selector, selectee = selectee, agenda = agenda, sentence_length = sentence_length, direction = 'left', adjoin = True, resultsExpressionList=resultsExpressionList, failure_messages=failure_messages, printPartialAnalyses=printPartialAnalyses)
    elif re.search(left_adjoin, selector.head_chain.features[0]):
        MERGE(selector = selector, selectee = selectee, agenda = agenda, sentence_length = sentence_length, direction = 'right', adjoin = True, resultsExpressionList=resultsExpressionList, failure_messages=failure_messages, printPartialAnalyses=printPartialAnalyses)
    elif resultsExpressionList != None:
        failure_messages.append("Illicit features detected.")

def MERGE(selector, selectee, agenda, sentence_length, direction, hm_dir = None, adjoin = False, excorp = False, resultsExpressionList=None, failure_messages=None, printPartialAnalyses=False):
    multiple_extraposers_exemption = False
    multiple_focalizers_exemption = False
    multiple_topicalizers_exemption = False
    if not adjoin:
        allow_merge = False
        if selector.ID in supertag_links:
            if str(len(selector.head_chain.checked_features)) in supertag_links[selector.ID]:
                if selectee.ID == supertag_links[selector.ID][str(len(selector.head_chain.checked_features))]:
                    allow_merge = True
            else:
                if selectee.ID not in supertag_links:
                    allow_merge = True
                else:
                    if str(len(selectee.head_chain.checked_features)) not in supertag_links[selectee.ID]:
                        allow_merge = True
        else:
            if selectee.ID not in supertag_links:
                allow_merge = True
            else:
                if str(len(selectee.head_chain.checked_features)) not in supertag_links[selectee.ID]:
                    allow_merge = True
        if not allow_merge:
            return
    if selector.head_chain.features[0] in ["=D", "=d", "d=", "D="]:
        dp_theta_checker = True
    else:
        dp_theta_checker = False
    if selectee.persist_selectee and dp_theta_checker:
        #a persistant selectee might have been created during merger with another constituent
        #and we may need to disallow that persistent selectee for this new selector
        if len(selector.head_chain.features) > 1 and selector.head_chain.features[1].lower() == '+case' and len(selectee.head_chain.features) > 1 and selectee.head_chain.features[1].lower() == '-case':
            found_anaphor = False
            for chain in selectee.non_head_chains:
                if chain.features[0].lower() == '-case' and 'ANA' in chain.subcatAgreeFeatures[0]:
                    found_anaphor = True
                    break
            if not found_anaphor:
                if resultsExpressionList != None:
                    failure_messages.append("Persistent selectee disallowed: selector checks theta+case and no anaphor found.")
                return
        #if there's already a d mover inside the selector, then we disallow external merge of a d
        for chain in selector.non_head_chains:
            if chain.features[0] in ['d', 'D']:
                if resultsExpressionList != None:
                    failure_messages.append("External merge of DP attempted when internal merge of DP available.")
                return
    if selector.saturated or (selectee.saturated and hm_dir != None):
        if resultsExpressionList != None:
            failure_messages.append("Illicit merger of saturated constituent attempted.")
        return
    lexical_coordinator = False
    if 'conj' in selector.cat_feature and len(selector.head_chain.checked_features)+len(selector.head_chain.features) > 3 and len(selector.head_chain.checked_features) <= 1:
        suffix_features = [f for f in [selector.head_chain.checked_features+selector.head_chain.features][0][2:]]
        for feature in suffix_features:
            if '=' in feature:
                lexical_coordinator = True
        if lexical_coordinator and not selectee.saturated:
            if resultsExpressionList != None:
                failure_messages.append("Attempted merger of lexical coordinator with non-saturated-head.")
            #lexical head coordinators can only combine with saturated conjuncts
            return
        elif lexical_coordinator and selectee.saturated:
            #if this is a coordinator with more than three features and the selector feature is one of the first two
            #for the comp and (mutliple) spec conjuncts, then if there are any further features
            #on the coordinator this must be a lexical head coordinator and we need to perform the
            #relevant matches to make sure this operation is allowed.
            if selectee.saturated:
                if len(selector.head_chain.checked_features) == 0:
                    #I was initially enforcing that all subcat features must match, but this would then
                    #incorrectly disallow coordination of past only with past/perf verbs.. plus you can
                    #marginally coordinate past with present verbs "Jack ate and likes bannanas"
                    #coordinator_subcat_feature_suffix = selector.head_chain.subcatAgreeFeatures[2:]
                    #if selectee.head_chain.oldSubcatAgreeFeatures != coordinator_subcat_feature_suffix:
                        #if resultsExpressionList != None:
                            #failure_messages.append("Feature sequence mismatch for lexical head coordination.")
                        #return
                    coordinator_feature_suffix = selector.head_chain.features[2:]
                elif len(selector.head_chain.checked_features) == 1:
                    #coordinator_subcat_feature_suffix = selector.head_chain.subcatAgreeFeatures[1:]
                    #if selectee.head_chain.oldSubcatAgreeFeatures != coordinator_subcat_feature_suffix:
                        #if resultsExpressionList != None:
                            #failure_messages.append("Feature sequence mismatch for lexical head coordination.")
                        #return
                    coordinator_feature_suffix = selector.head_chain.features[1:]
                selectee_feature_sequence = []
                for f in selectee.head_chain.checked_features:
                    selectee_feature_sequence.append(f)
                selectee_feature_sequence.append(selectee.head_chain.features[0])
                for f in selectee.licensees:
                    selectee_feature_sequence.append(f)
                if selectee_feature_sequence != coordinator_feature_suffix:
                    if resultsExpressionList != None:
                        failure_messages.append("Feature sequence mismatch for lexical head coordination.")
                    return
            else:
                if resultsExpressionList != None:
                    failure_messages.append("Selectee must be type-saturated for lexical head coordination.")
                return
    elif selectee.saturated and not adjoin:
        if resultsExpressionList != None:
            failure_messages.append("Conditions for merger of type-saturated constituent unmet.")
        return
    #since adjunction always leads to the selectee feature persisting, we disallow
    #separate derivations for this as we have for normal selection when the selectee persists
    #This is because we want to avoid spurious ambiguity here..
    escape = False
    if adjoin == True and selectee.persist_selectee == True:
        return
    mother_w_persist_selector = None
    if selector.head_chain.head_string == '[extraposer]' and selectee.head_chain.head_string == '[op]':
        #I assume that operators in tough movement never undergo rightward movement.. this speeds to parser up considerably..
        if resultsExpressionList != None:
            failure_messages.append("Merger of [op] with [extraposer] is disallowed.")
        return
    #we can immediately abort if the selectee has no phonetic content and is a dependent of a conjP.. this prevents infinite recursion of null specs
    #in conjP
    if 'conj' in selector.cat_feature and selectee.head_chain.string.narrow_yield.get_span() == [[], []] and selectee.head_chain.string.head_yield[0].get_span() == [[], []]:
        if resultsExpressionList != None:
            failure_messages.append("Null conjuncts are disallowed.")
        return
    if adjoin == True and selector.head_chain.string.narrow_yield.get_span() == [[], []] and selector.head_chain.string.head_yield[0].get_span() == [[], []]:
        #we don't want null adjuncts!  Owing to EDGE exception to CED + ATB exception, null adjuncts (i.e. those whose head has a null span) can lead to infinite recursion if they contain a mover exempted from CED by EDGE
        if resultsExpressionList != None:
            failure_messages.append("Null adjuncts are disallowed.")
        return
    if hm_dir != None:
        #we abort if this is adjunction or if the selectee is a specifier, except in the spec case where the governor
        #is a conjunction
        if adjoin == True or (selector.sc not in ["::", ":\u0305:\u0305"] and 'conj' not in selector.head_chain.cat_feature):
            if resultsExpressionList != None:
                failure_messages.append("Head movement out of specifier or adjunct is disallowed.")
            return
    #THE ADJACENCY CHECKS BETWEEN SPEC-HEAD-COMP ARE ONLY POSSIBLE IF ADJUNCTS ARE BANNED FROM
    #ADJOINING TO XBAR, AS IN CHOMSKY 1986.
    #perform a quick check to make sure that the selector is a head, otherwise reject this merge operation
    ignore_dependent_chains = False
    ATB_drop = False
    #if selectee's first feature is strong, then it must be allowed to optionally persist (for control).  To achieve this,
    #we create a copy of selectee with an attribute indicating that it is to persist, and add it to the agenda..
    #then we just process the current original selectee as a non-persistent selectee.  We do not do this if the
    #selector is a conjunction, however, since allowing conjuncts to be extracted would violate the
    #coordinate structure constraint..(ATB is handled separately by dropping one of the duplicate movers
    #and has already been done by this stage.. we also have to make sure that conjunctions can't merge
    #with persistent selectees that were eneterd into the chart when their non-persistent versions merged with another head
    #such as a null [dat] head..
    if 'conj' in selector.head_chain.cat_feature and selectee.persist_selectee == True:
        return
    #Captial letter D may persist unless the head selecting for D also has a +CASE/+case feature immediately behind its =d/=D/d=/D= and the selectee has a -case behind its D.. in other words, case and theta must be checked simultaneously wherever possible
    #The one exception to this is the case of anaphors (reflexives and reciprocals) which are considered here to be additional case checkers (Hornstein 2001).. so we allow this scenario only in the case where there
    #is an anaphor inside the selectee ready to check the case feature of the verb head in question in the next derivational step.
    if selectee.persist_selectee:
        if 'conj' in selector.cat_feature:
            return
        allow_persist_selectee = True
        if len(selector.head_chain.features) > 1 and selector.head_chain.features[1].lower() == '+case' and len(selectee.head_chain.features) > 1 and selectee.head_chain.features[1].lower() == '-case':
            allow_persist_selectee = False
            for chain in selectee.non_head_chains:
                if chain.features[0].lower() == '-case' and 'ANA' in chain.subcatAgreeFeatures[0]:
                    alow_persist_selectee = True
                    break
        if not allow_persist_selectee:
            return
    atb_chain_pairs = []
    if selector.sc != "::" and selector.sc != ":\u0305:\u0305":
        if direction == 'right' and adjoin == False:
            if resultsExpressionList != None:
                failure_messages.append("Rightward specifiers are disallowed.")
            return
        if not adjoin:
            nhc = selectee.non_head_chains
        else:
            nhc = selector.non_head_chains
        if not adjoin:
            if len(nhc) > 0:
                escape = True
            else:
                escape = False
            for chain in nhc:
                if 'EDGE' not in chain.subcatAgreeFeatures[0]:
                    escape = False
                    break
        else:
            escape = False
        #the following instantiates the spec part of CED for externally merged specs and adjunct part of CED (Huang 1982)
        if (len(selectee.non_head_chains) > 0 and not adjoin) or (len(selector.non_head_chains) > 0 and adjoin == True):
            #if every non_head_chain inside the selectee (selector for adjunction) exactly matches some
            #chain inside the selector (selectee for adjunction), we allow the merge and simply drop the chain from the selectee (selector for adjunction).. this allows ATB
            #and RNR (treated here as rightwards ATB)..
            if adjoin == False:
                dependent = selectee
                governor = selector
            else:
                dependent = selector
                governor = selectee
            if (dependent.head_chain.string.narrow_yield.get_span() != [[],[]] or dependent.head_chain.string.head_yield[0].get_span() != [[],[]]) and (governor.head_chain.string.narrow_yield.get_span() != [[],[]] or governor.head_chain.string.head_yield[0].get_span() != [[],[]] or governor.head_chain.head_string == '[pro-v]'):
                #to avoid cases of infinite recursion, we enforce that both the dependent and governor
                #must have either an overt narrow yield or overt head yield (governor which are ellipsis heads are also allowed)
                atb_allowed = True
            else:
                atb_allowed = False
            chain_index = -1
            M = False
            for non_head_chain in dependent.non_head_chains:
                match = False
                if atb_allowed:
                    for chain in governor.non_head_chains:
                        #only check span identity, not string identity as this includes null [xxx] heads that can mess things up
                        if chain.string.narrow_yield.get_yield()[1] == non_head_chain.string.narrow_yield.get_yield()[1]:
                            if features_identical(chain.features, non_head_chain.features) and not case_conflict(chain.checked_features, non_head_chain.checked_features):
                                match = True
                                M = True
                                ATB_drop = True
                                atb_chain_pairs.append((chain, non_head_chain))
                                if chain.head_string == '[extraposer]':
                                    multiple_extraposers_exemption = True
                                elif chain.head_string == '[focalizer]':
                                    multiple_focalizers_exemption = True
                                elif chain.head_string == '[topicalizer]':
                                    multiple_topicalizers_exemption = True
                                break
                if match == False and not escape:
                    dependent_narrow_yield = dependent.head_chain.string.narrow_yield.get_span()
                    if adjoin and ('c=' not in dependent.head_chain.checked_features and '=c' not in dependent.head_chain.checked_features and 't=' not in dependent.head_chain.checked_features and '=t' not in dependent.head_chain.checked_features):
                        #Adjunct islands only apply for adjunct clauses
                        escape = True
                    elif not adjoin and 'IT' in dependent.head_chain.subcatAgreeFeatures[0]:
                        #we allow things to escape from 'it-cp' clauses: "what is it difficult to know?'
                        escape = True
                    else:
                        if resultsExpressionList != None:
                            failure_messages.append("Attempted violation of specifier/adjunct island constraint.")
                        return
            if M == True:
                ignore_dependent_chains = True
    #the following instantiates the part of the coordinate structure constraint which prevents
    #extraction of a conjunct..the second part, which prohibits extraction FROM
    #a single conjunct, will be handled separately (as part of the leftward ATB algorithm).
    if 'conj' in selector.cat_feature:
        if len(selectee.head_chain.features) > 1 and selectee.head_chain.features[0].lower() != 'part' and selectee.head_chain.features[1].lower() != '-foc':
            if resultsExpressionList != None:
                failure_messages.append("Coordinate Structure Constraint violation: extraction of conjunct.")
            return
        if selector.sc != "::" and selector.sc != ":\u0305:\u0305":
            if len(selector.non_head_chains) != len(selectee.non_head_chains):
                if resultsExpressionList != None:
                    failure_messages.append("Coordinate Structure Constraint violation: one conjunct has more movers.")
                return
    #we'll start with a copy of the selector for the mother (or selectee of adjoin == True) and then modify it
    if adjoin == False:
        mother = copy_expression(selector)
    else:
        mother = copy_expression(selectee)
    mother.outside_cost = None#this will be set properly later, in add_to_agenda()
    if selector.is_overt or selectee.is_overt:
        mother.is_overt = True
    mother.inside_cost = Decimal(selector.inside_cost+selectee.inside_cost)
    #ATB movement involves the dropping of spans.. we must therefore deduct some cost from mother..
    #however, to ensure monotonic increase in item costs, we must only drop the lowest of the
    #two atb items' costs.. two items unified under atb can have different costs if they are anchors for different
    #supertags (i.e. are in supertags with different null heads, but same overt head)
    if not excorp:
        if hm_dir != None:
            mother.head_chain.head_inside_cost = Decimal(selectee.head_chain.head_inside_cost+selector.head_chain.head_inside_cost)
    else:
        if selector.sc in [":", ":\u0305"]:
            #the case of atb head drop
            to_deduct = min(selector.head_chain.head_inside_cost, selectee.head_chain.head_inside_cost)
            mother.inside_cost -= to_deduct
            mother.head_chain.head_inside_cost -= to_deduct
        else:
            #the case of head movement with excorporation (the selectee's head string becomes the head string of mother)
            mother.head_chain.head_inside_cost = Decimal(selectee.head_chain.head_inside_cost)
    for chain_pair in atb_chain_pairs:
        mother.inside_cost -= min(chain_pair[0].inside_cost, chain_pair[1].inside_cost)
    if not adjoin:
        mother.head_chain.inside_cost = selector.head_chain.inside_cost
    else:
        mother.head_chain.inside_cost = selectee.head_chain.inside_cost
    if mother.sc in ['::', ':\u0305:\u0305'] and mother.head_chain.string.narrow_yield.get_span() == [[],[]]:
        #we convert all null [xxxx] heads to u'\u03b5' (epsilon) in the derivation tree except for the terminal nodes themselves (we keep these becase 1. it makes the derivation trees easier to read; 2. because gen_derived_tree.py needs
        #them to construct the phrase structure trees..
        mother.head_chain.string.narrow_yield.get_string()[1][0].set_string(u'\u03b5')
        mother.head_chain.string.head_yield[0].set_string(u'\u03b5')
    #now we check that the fine-grained selectional requirements of the selector are met..
    variable_found = False
    suppressed_subcats = []
    if selector.head_chain.subcatAgreeFeatures[0] != []:
        for subcatAgreeFeature in selector.head_chain.subcatAgreeFeatures[0]:
            if subcatAgreeFeature in sel_variables:
                variable_found = True
                variable = subcatAgreeFeature
            else:
                fork = re.search('\[.*?\|.*?\]', subcatAgreeFeature)
                if fork:
                    options = fork.group(0)[1:-1].split("|")
                match_found = False
                if '+' == subcatAgreeFeature[0]:
                    if fork:
                        #we allow the user to specify that a selectee
                        #can have one of a number of options.  This allows us to to say, e.g., that a prepositional
                        #object can be either GEN or ACC (but must not be NOM).
                        for sf in options:
                            if sf in selectee.head_chain.subcatAgreeFeatures[0]:
                                match_found = True
                                break
                    if not match_found and subcatAgreeFeature[1:] not in selectee.head_chain.subcatAgreeFeatures[0]:
                        if resultsExpressionList != None:
                            failure_messages.append("c-selectional (subcategorization) or agreement requirements not met.")
                        return
                elif '-' == subcatAgreeFeature[0]:
                    match_found = True
                    if fork:
                        #not sure if this is needed but will do something similar for the neg
                        #case where only one of the things need be absent to get a match, not all
                        for sf in options:
                            if sf not in selectee.head_chain.subcatAgreeFeatures[0]:
                                match_found = False
                                break
                            elif sf in selectee.head_chain.subcatAgreeFeatures[0]:
                                #if the subcat feature is part of a paradigm then we may have a case of
                                #syncretism, in which case we do not want -NOM to abort the derivation just because
                                #the mover has a NOM feature IFF it also has an ACC or GEN feature etc and there is no -ACC or -GEN in the selector too.. same for phi features
                                paradigm = None
                                for p in paradigms:
                                    if sf in p:
                                        paradigm = p
                                        break
                                if paradigm != None:
                                    BREAK = False
                                    for f in selectee.head_chain.subcatAgreeFeatures[0]:
                                        if f != sf and f in paradigm:
                                            match_found = False
                                            BREAK = True
                                            break
                                    if BREAK:
                                        break
                    else:
                        if subcatAgreeFeature[1:] not in selectee.head_chain.subcatAgreeFeatures[0]:
                            match_found = False
                        elif subcatAgreeFeature[1:] in selectee.head_chain.subcatAgreeFeatures[0]:
                            paradigm = None
                            for p in paradigms:
                                if subcatAgreeFeature[1:] in p:
                                    paradigm = p
                                    break
                            if paradigm != None:
                                for f in selectee.head_chain.subcatAgreeFeatures[0]:
                                    if f != subcatAgreeFeature[1:] and f in paradigm and '-'+f not in selector.head_chain.subcatAgreeFeatures[0]:
                                        match_found = False
                                        break
                    if match_found:
                        if resultsExpressionList != None:
                            failure_messages.append("c-selectional (subcategorization) or agreement requirements not met.")
                        return
                elif "~" == subcatAgreeFeature[0]:
                    suppressed_subcats.append(subcatAgreeFeature)
                else:
                    if fork:
                        abort = True
                        #the case where the +/- is inside not outside the OR brackets
                        for sf in options:
                            if sf[0] == "+":
                                if sf[1:] in selectee.head_chain.subcatAgreeFeatures[0]:
                                    abort = False
                                    break
                            elif sf[0] == "-":
                                if sf[1:] not in selectee.head_chain.subcatAgreeFeatures[0]:
                                    abort = False
                                    break
                                elif sf[1:] in selectee.head_chain.subcatAgreeFeatures[0]:
                                    paradigm = None
                                    for p in paradigms:
                                        if subcatAgreeFeature[1:] in p:
                                            paradigm = p
                                            break
                                    if paradigm != None:
                                        for f in selectee.head_chain.subcatAgreeFeatures[0]:
                                            if f != sf[1:] and f in paradigm:
                                                abort = False
                                                break
                        if abort:
                            if resultsExpressionList != None:
                                failure_messages.append("c-selectional (subcategorization) or agreement requirements not met.")
                            return
    #we need a record of what mother's subcat features are now because we will restore them in case this mother has a selector
    #feature which persists and is therefore a coordinator, because following Zhang I assume that only the leftmost
    #specifier projects..
    old_mother_subcatAgreeFeatures = copy.deepcopy(mother.head_chain.subcatAgreeFeatures)
    if variable_found == True:
        #if a variable was found in the selector's first set of selectional features, then the
        #selectee's selectional features must replace this variable in all other sets of selectional features on the selector
        #which also have this variable...this corresponds to simply passing e.g. the lexical verbs PAST feature onto
        #little v.  In the case of adjunction, the only possible scenario under which this might have an effect would
        #we where the adjunct then moves and the feature was copied onto one of its licensees..
        #if the selecting head is a coordator, we do not pass 3SG, as coordinated nominal structures are 3PL..
        #we also do not pass COORD or EXCORP up as obviously these properties do not apply to higher constituents
        j=-1
        for subcatAgreeFeatures in mother.head_chain.subcatAgreeFeatures:
            j+=1
            for f in subcatAgreeFeatures:
                if variable == f:
                    for subcatAgreeFeature in selectee.head_chain.subcatAgreeFeatures[0]:
                        if not ('conj' in selector.cat_feature and subcatAgreeFeature == '3SG') and subcatAgreeFeature not in sel_variables and subcatAgreeFeature not in subcatAgreeFeatures and "~"+subcatAgreeFeature not in suppressed_subcats and subcatAgreeFeature not in ['COORD', 'LH', 'EXCORP']:
                            if mother.head_chain.features[j].lower() in ['+pers', '+num']:
                                if subcatAgreeFeature[0] == "+":
                                    if subcatAgreeFeature[1:] in agreement_features:
                                        pers = subcatAgreeFeature[:2]
                                        num = "+"+subcatAgreeFeature[2:]
                                        if mother.head_chain.features[j].lower() == '+pers':
                                            subcatAgreeFeatures.append(pers)
                                        else:
                                            subcatAgreeFeatures.append(num)
                            else:
                                subcatAgreeFeatures.append(subcatAgreeFeature)
            subcatAgreeFeatures.sort()
        for item in mother.head_chain.subcatAgreeFeatures:
            if variable in item:
                item.remove(variable)
    #if the selector is a head, then we need to delete the mother's narrow yield as this will be set to the head's narrow yield
    #and the head may move.. mother's narrow yield will then be set to the complement's narrow yield if it has one which is not moving
    if mother.sc in ['::', ':\u0305:\u0305']:
        mother.head_chain.string.narrow_yield.set_span([[], []])
    #we fuse the spec-head-comp parts of the selectee (the selector if this is adjunction) (ignoring the head if head movement
    #is taking place) and we also at this point check for the correct adjacency relations between the parts, and if they are good,
    #fuse them into a new single span..if they are bad we reject this merge operation.
    if adjoin == False:
        fusee = selectee.head_chain.string.narrow_yield.get_string()
    else:
        fusee = selector.head_chain.string.narrow_yield.get_string()
    fused_string = ""
    fusee_start = 10000
    fusee_end = -1
    position = None
    real_position = None
    epsilon_found = False
    for part in fusee:
        if len(part) > 0:
            STRING = part[0].get_string()
            if STRING == u'\u03b5':
                epsilon_found = True
                continue
            if STRING != '':
                if hm_dir != None and part == selectee.head_chain.string.head_yield:
                    #insert head movement trace
                    x=0
                else:
                    fused_string += STRING+" "
                    part_start = part[0].get_span()[0]
                    part_end = part[0].get_span()[1]
                    if position ==  None:
                        #the first time around we do not need to do the position check as there is nothing
                        #preceding the first part
                        x=0
                    else:
                        if position != part_start and not (part_start == []):
                            if position == []:
                                if real_position != None and real_position != part_start:
                                    if resultsExpressionList != None:
                                        failure_messages.append("selectee string (left-dep, head, right-dep) adjacency checks failed.")
                                    return
                            elif position != part_start:
                                if resultsExpressionList != None:
                                    failure_messages.append("selectee string (left-dep, head, right-dep) adjacency checks failed.")
                                return
                    #in case position gets set to [] we need to be able to look back to the last true position if there is one
                    position = part_end
                    if position != []:
                        real_position = position
                    #the idea here is to collect any reified position indices if they occur, but if they don't to
                    #preserve the position variables [[], []]
                    if fusee_start == []:
                        fusee_start = part_start
                    elif part_start != [] and part_start < fusee_start:
                        fusee_start = part_start
                    if fusee_end == []:
                        fusee_end = part_end
                    elif part_end != [] and part_end > fusee_end:
                        fusee_end = part_end
    if fused_string == "" and epsilon_found:
        fused_string = u'\u03b5'
    if fusee_end == -1:
        #if this selectee was empty then its narrow yield span and strings are empty, so we set the
        #fused span to be [[], []]
        fused_span = [[], []]
    else:
        fused_span = [fusee_start, fusee_end]
    #if we are using PTB/CCG spans to constrain the parser's search space, this is implemented here..
    #there are some exceptions, such as for NAME NPs which in MGbank have the opposite constituency..
    #we alsoexempt adjunction because these spans will be captured anyway when the adjunctizer takes the
    #overt material as its complement and we can't detect the NAME property at the point where adjunction
    #is taking place..Because of rightward movement to TP, for clauses we wait until the TP is complete before
    #checking constituency except for VP which we check..
    if source_spans != None:
        if selectee.head_chain.features[0].lower() in ['d', 'p', 'c', 't', 'v', 'n'] and not adjoin and fused_span != [[],[]] and selectee.head_chain.head_string not in ['[wh]', '[relativizer]', '[nom]'] and hm_dir == None:
            selectee_subcats = [sf for sf in selectee.head_chain.subcatAgreeFeatures[0]]
            if selector.cat_feature.lower() not in ['q'] and 'FRAG' not in selector.head_chain.cat_subcats and 'NAME' not in selectee_subcats and 'DITRANS' not in selectee_subcats and 'RELAT' not in selectee_subcats and 'PART' not in selectee_subcats:
                if fused_span not in source_spans[fused_span[0]]:
                    if resultsExpressionList != None:
                        failure_messages.append("Attempted merge resulting in dependent constituent not\nmatching any constituent in the PTB or CCG trees!")
                    return
    if 'conj' in selector.cat_feature and fused_span == [[], []]:
        #all conjuncts should have some overt span.. this prevents infinite recursion of null conjuncts..
        if resultsExpressionList != None:
            failure_messages.append("Null conjuncts are disallowed.")
        return
    #now strip off any whitespace from the end of the fused string
    if len(fused_string) > 0 and fused_string[-1] == " ":
        fused_string = fused_string[:-1]
    #now perform head movement if necessary (not relevant in the adjunction case)
    if (hm_dir != None or (selectee.saturated and not adjoin)) and excorp == False:
        selector_head_string = selector.head_chain.string.head_yield[0].get_string()
        selector_head_span = selector.head_chain.string.head_yield[0].get_span()
        selectee_head_string = selectee.head_chain.string.head_yield[0].get_string()
        selectee_head_span = selectee.head_chain.string.head_yield[0].get_span()
        if hm_dir == 'left' or (selectee.saturated and direction == 'left'):
            #a quick adjacency check
            if [[], []] not in [selector_head_span, selectee_head_span] and selectee_head_span[1] != selector_head_span[0]:
                if resultsExpressionList != None:
                    failure_messages.append("String adjacency check failure for attempted head movement.")
                return
            if selectee_head_span == selector_head_span == [[],[]]:
                mother.head_chain.string.head_yield[0].set_yield(u'\u03b5', [[],[]])
            elif selectee_head_span == [[], []]:
                selectee_head_span = [selector_head_span[0], selector_head_span[0]]
                mother.head_chain.string.head_yield[0].set_yield(selector_head_string, [selectee_head_span[0], selector_head_span[1]])
            elif selector_head_span == [[], []]:
                selector_head_span = [selectee_head_span[1], selectee_head_span[1]]
                mother.head_chain.string.head_yield[0].set_yield(selectee_head_string, [selectee_head_span[0], selector_head_span[1]])
            else:
                mother.head_chain.string.head_yield[0].set_yield(selectee_head_string+" "+selector_head_string, [selectee_head_span[0], selector_head_span[1]])
        elif hm_dir == 'right' or (selectee.saturated and direction == 'right'):
            if [[], []] not in [selector_head_span, selectee_head_span] and selectee_head_span[0] != selector_head_span[1]:
                if resultsExpressionList != None:
                    failure_messages.append("String adjacency check failure for attempted head movement.")
                return
            if selectee_head_span == selector_head_span == [[],[]]:
                mother.head_chain.string.head_yield[0].set_yield(u'\u03b5', [[],[]])
            elif selectee_head_span == [[], []]:
                selectee_head_span = [selector_head_span[1], selector_head_span[1]]
                mother.head_chain.string.head_yield[0].set_yield(selector_head_string, [selector_head_span[0], selectee_head_span[1]])
            elif selector_head_span == [[], []]:
                selector_head_span = [selectee_head_span[0], selectee_head_span[0]]
                mother.head_chain.string.head_yield[0].set_yield(selectee_head_string, [selector_head_span[0], selectee_head_span[1]])
            else:
                mother.head_chain.string.head_yield[0].set_yield(selector_head_string+" "+selectee_head_string, [selector_head_span[0], selectee_head_span[1]])
    if excorp == True:
        if adjoin:
            if resultsExpressionList != None:
                failure_messages.append("Excorporation from adjuncts is disallowed.")
            return
        if selector.sc in [":", ":\u0305"]:
            #this must be the case where it is the head of the specifier that is excorporating
            #so we need to look for atb head drop
            hm_dir = 'atb'
            #we only want to check span identity not string identity.. this is to allow, e.g. 'be' first merged in V and 'be' first merged in v to undergo atb head movement when remnant vP is coordinated (for unlike constituent coordination), even though one as an extra null head to which it has already adjoined
            if selector.head_chain.string.head_yield[0].get_span() != selectee.head_chain.string.head_yield[0].get_span():
                if resultsExpressionList != None:
                    failure_messages.append("String identity check failure for attempted ATB head movement.")
                return
        else:
            #this is the case where the excorporating head is coming from the complement so now
            #we transfer and later fuse the existing selector's head to the left edge of its right dependents (which will be the complement below)
            #and make the excorporating head the new head of the governor.. (see Torr and Stabler 2016)
            xhead_yield = Yield(string=selectee.head_chain.string.head_yield[0].get_string(), span=selectee.head_chain.string.head_yield[0].get_span())
            mother.head_chain.string.r_dependent_yields.insert(0, mother.head_chain.string.head_yield[0])
            del(mother.head_chain.string.head_yield[0])
            mother.head_chain.string.head_yield.append(xhead_yield)
            mother.head_string = selectee.head_string
            mother.head_chain.head_string = selectee.head_string
    #now check whether the selectee has any licensee features to be checked, meaning it will be moving later..
    #for adjuncts, we check the selector's (=the adjunct's) head chain as it may move..
    if ((adjoin == False and len(selectee.head_chain.features) == 1 and selectee.persist_selectee == False) or (adjoin == True and len(selector.head_chain.features) == 1) and selector.persist_selectee == False):
        #the dependent is not moving...
        if not adjoin:
            mother.head_chain.inside_cost += selectee.head_chain.inside_cost
        else:
            mother.head_chain.inside_cost += selector.head_chain.inside_cost
        if direction == 'right' and adjoin == False:
            if mother.sc != "::" and mother.sc != ":\u0305:\u0305":
                #only complements and adjuncts may adjoin to the right, not spec..
                if resultsExpressionList != None:
                    failure_messages.append("Rightward specifiers are disallowed.")
                return
            #put this fused yield in as the complement yield of mother and set mother's narrow yield span to be that of
            #the complement (we don't include the head's yield span as this may move and no spec exists at this point)
            if not selectee.saturated:
                #if selectee is saturated then it will have been attached to the head of the selecting head coordinator
                #because the lexical head coordinator plus its conjuncts must behave as a unit with respect
                #to later head movement, e.g. 'likes and hates' must undergo V-to-v head movement as a unit
                mother.head_chain.string.r_dependent_yields.append(Yield(fused_string, fused_span))
                if fuse_dependents(mother.head_chain.string.l_dependent_yields, mother.head_chain.string.r_dependent_yields, check_dir = 'right', mother = mother) == False:
                    if resultsExpressionList != None:
                        failure_messages.append("String adjacency check failure for attempted merger of complement.")
                    return
            mother.head_chain.string.narrow_yield.set_span(fused_span)
        elif direction == 'right' and adjoin == True:
            mother.head_chain.string.l_dependent_yields.insert(0, Yield(fused_string, fused_span))
            if fuse_dependents(mother.head_chain.string.l_dependent_yields, mother.head_chain.string.r_dependent_yields, check_dir = 'left', mother = mother) == False:
                if resultsExpressionList != None:
                    failure_messages.append("String adjacency check failure for attempted merger of adjunct.")
                return
            #now find leftmost and rightmost dependents in narrow_yield.string and take their starting
            #and ending spans respectively as the narrow_yield_span (there was no need to do this for
            #complements as they are the first dependents merged and hence their span = mother's span (owing to
            #possible head movement, we don't count the head's span)
            #for some reason for adjuncts the yield of the dependent was not ending up in the
            #narrow yield of the mother, at least in some cases.. e.g. "Jack gave himself a present" gave messed up parses
            mother.head_chain.string.narrow_yield.string[0] = [mother.head_chain.string.l_dependent_yields[0]]
            (left_pos, right_pos) = find_narrow_yield(mother)
            mother.head_chain.string.narrow_yield.set_span([left_pos, right_pos])
        elif direction == 'left' and adjoin == True:
            mother.head_chain.string.r_dependent_yields.append(Yield(fused_string, fused_span))
            if not fuse_dependents(mother.head_chain.string.l_dependent_yields, mother.head_chain.string.r_dependent_yields, check_dir = 'right', mother = mother):
                if resultsExpressionList != None:
                    failure_messages.append("String adjacency check failure for attempted merger of adjunct.")
                return
            #now find leftmost and rightmost dependents in narrow_yield.string and take their starting
            #and ending spans respectively as the narrow_yield_span
            mother.head_chain.string.narrow_yield.string[2] = [mother.head_chain.string.r_dependent_yields[0]]
            (left_pos, right_pos) = find_narrow_yield(mother)
            mother.head_chain.string.narrow_yield.set_span([left_pos, right_pos])
        elif mother.sc in ['::', ':\u0305:\u0305']:
            #this is a left merged complement
            if not selectee.saturated:
                mother.head_chain.string.l_dependent_yields.insert(0, Yield(fused_string, fused_span))
                if not fuse_dependents(mother.head_chain.string.l_dependent_yields, mother.head_chain.string.r_dependent_yields, check_dir = 'left', mother = mother):
                    if resultsExpressionList != None:
                        failure_messages.append("String adjacency check failure for attempted merger of complement.")
                    return
            mother.head_chain.string.narrow_yield.set_span(fused_span)
        else:
            #this is a left merged specifier..
            if not selectee.saturated:
                mother.head_chain.string.l_dependent_yields.insert(0, Yield(fused_string, fused_span))
                if fuse_dependents(mother.head_chain.string.l_dependent_yields, mother.head_chain.string.r_dependent_yields, check_dir = 'left', mother = mother) == False:
                    if resultsExpressionList != None:
                        failure_messages.append("String adjacency check failure for attempted merger of specifier.")
                    return False
            #now find leftmost and rightmost dependents in narrow_yield.string and take their starting
            #and ending spans respectively as the narrow_yield_span
            (left_pos, right_pos) = find_narrow_yield(mother)
            mother.head_chain.string.narrow_yield.set_span([left_pos, right_pos])
        #delete the selector feature of mother (as the selectee is not moving, it cannot have any further features
        #unless it was the modified element in an adjunct config, in which case its head chain has already been transferred to mother)
        #we do not do this in the case of adjunction, since the X≈ feature was already left behind when we
        #replaced the selector derived features with the selectee derived features in mother
        if adjoin == False:
            #checking for adjuncts is asymmetric - only the adjunct's feature is checked.. and since any
            #adjunct here is not moving, it's head features will not be transferred into mother's expression anyway,
            #hence there is nothing to delete for adjuncts..
            mother.head_chain.checked_features.append(mother.head_chain.features[0])
            #for coordination, we must allow optional additional externally merged specifiers for e.g. examples like
            #"Jack, Pete Mary and Phil"..  Since it is never possible to extract only one of these, we only need to deal with
            #this in this section of the code.. we simply optionally allow the =d or =c feature to persist by creating a copy
            #whose feature is not deleted..This only applies for second merge (ie spec not comp) of course..
            if mother.sc not in ["::", ":\u0305:\u0305"] and 'conj' in mother.head_chain.cat_feature and direction == 'left' and not (selectee.head_chain.features[0] == 'part' and 'FOC' in selectee.head_chain.subcatAgreeFeatures[0]):
                mother_w_persist_selector = copy_expression(mother)
                mother_w_persist_selector.head_chain.subcatAgreeFeatures = old_mother_subcatAgreeFeatures
                del(mother_w_persist_selector.head_chain.checked_features[-1])
            del(mother.head_chain.features[0])
            del(mother.head_chain.subcatAgreeFeatures[0])
        #append all chains of the selectee except for the head chain (whose features must be exhausted), to the mother expression
        #we make 'deep' copies of the chains as we may need to modify them in move.. however, we want to keep the original spans as they
        #may contain [] position variables.. we don't use deepcopy as copies stuff we don't need.. 
        if adjoin == False:
            if ignore_dependent_chains == False:
                #any movers exempted from CED are now transferred into mother
                for chain in selectee.non_head_chains:
                    chain_copy = copy_chain(chain)
                    mother.non_head_chains.append(chain_copy)
            if direction == 'right':
                mother.pointers.append(({'split':False, 'lex_head_coord':selectee.saturated and not adjoin, 'operation':'merge', 'phonetic_merge':False, 'adjoin':adjoin, 'hm_dir':hm_dir, 'direction':direction, 'persist_selectee':selectee.persist_selectee, 'ATB_drop':ATB_drop, 'persist_selector':False, 'escape':escape}, selector, selectee))
            else:
                mother.pointers.append(({'split':False, 'lex_head_coord':selectee.saturated and not adjoin, 'operation':'merge', 'phonetic_merge':False, 'adjoin':adjoin, 'hm_dir':hm_dir, 'direction':direction, 'persist_selectee':selectee.persist_selectee, 'ATB_drop':ATB_drop, 'persist_selector':False, 'escape':escape}, selectee, selector))
            if mother_w_persist_selector != None:
                if ignore_dependent_chains == False:
                    for chain in selectee.non_head_chains:
                        chain_copy = copy_chain(chain)
                        mother_w_persist_selector.non_head_chains.append(chain_copy)
                if direction == 'right':
                    mother_w_persist_selector.pointers.append(({'split':False, 'lex_head_coord':selectee.saturated and not adjoin, 'operation':'merge', 'phonetic_merge':False, 'adjoin':adjoin, 'hm_dir':hm_dir, 'direction':direction, 'persist_selectee':selectee.persist_selectee, 'ATB_drop':ATB_drop, 'persist_selector':True, 'escape':escape}, selector, selectee))
                else:
                    mother_w_persist_selector.pointers.append(({'split':False, 'lex_head_coord':selectee.saturated and not adjoin, 'operation':'merge', 'phonetic_merge':False, 'adjoin':adjoin, 'hm_dir':hm_dir, 'direction':direction, 'persist_selectee':selectee.persist_selectee, 'ATB_drop':ATB_drop, 'persist_selector':True, 'escape':escape}, selectee, selector))
        else:
            if ignore_dependent_chains == False:
                #any movers exempted from CED are now transferred into mother
                for chain in selector.non_head_chains:
                    chain_copy = copy_chain(chain)
                    mother.non_head_chains.append(chain_copy)
            #in the case of adjuncts, we treat the selectee as the head..
            if direction == 'right':
                mother.pointers.append(({'split':False, 'lex_head_coord':selectee.saturated and not adjoin, 'operation':'merge', 'phonetic_merge':False, 'adjoin':adjoin, 'hm_dir':hm_dir, 'direction':direction, 'persist_selectee':False, 'ATB_drop':ATB_drop, 'persist_selector':False, 'escape':escape}, selector, selectee))
            else:
                mother.pointers.append(({'split':False, 'lex_head_coord':selectee.saturated and not adjoin, 'operation':'merge', 'phonetic_merge':False, 'adjoin':adjoin, 'hm_dir':hm_dir, 'direction':direction, 'persist_selectee':False, 'ATB_drop':ATB_drop, 'persist_selector':False, 'escape':escape}, selectee, selector))
        if mother.sc in [':\u0305:\u0305', ':\u0305']:
            mother.sc = ':\u0305'
            if selectee.saturated and len(mother.head_chain.checked_features) == 2:
                #this must be a lexical head coordinator that has all its conjuncts in place..
                #we therefore now transform it back to a lexical head type :: (so that it can take a rightward
                #complement given that rightward specs are banned)
                mother.sc = "::"
                mother.was_coordinator = True
                #we must also remove the -conj tag from mother's cat_feature as mother is no longer
                #a coordinator
                mother.cat_feature = re.sub('-conj', '', mother.cat_feature)
        else:
            mother.sc = ':'
        #sorting chains ensures that expressions are properly comparable..
        mother.non_head_chains = sorted(mother.non_head_chains, key=lambda x: x.string.narrow_yield.span)
        if resultsExpressionList == None:
            add_to_agenda(item = mother, agenda = agenda, sentence_length = sentence_length, merge_arg1=selector, merge_arg2=selectee, printPartialAnalyses=printPartialAnalyses)
        else:
            resultsExpressionList.append(mother)
        if mother_w_persist_selector != None:
            if mother.sc in [':\u0305:\u0305', ':\u0305']:
                mother_w_persist_selector.sc = ':\u0305'
            else:
                mother_w_persist_selector.sc = ':'
            mother_w_persist_selector.non_head_chains = sorted(mother_w_persist_selector.non_head_chains, key=lambda x: x.string.narrow_yield.span)
            if resultsExpressionList == None:
                add_to_agenda(item = mother_w_persist_selector, agenda = agenda, sentence_length = sentence_length, merge_arg1=selector, merge_arg2=selectee, printPartialAnalyses=printPartialAnalyses)
            else:
                resultsExpressionList.append(mother_w_persist_selector)
        return
    else:
        #here is the code for if the dependent is moving...
        #I removed the CED constraint for internally merged specs which prevented a complement which contained movers from moving itself..
        #the reason is that we don't know whether the movers inside the complement will vacate that complement
        #before it becomes a specifier.. and since it is always possible to move them out before anyway, this
        #constraint would easily be violable.  The problem is that MGs don't keep track of the geometry of the trees.
        #for each instance of movement, we create a covert and an overt version and let the system filter out the wrong one
        #in subsequent derivational steps..this avoids having to have separate covert and overt movement triggering licensees.. 
        #we disallow covert rightward movement here, since all rightward movement is assumed to be phonetic
        if adjoin:
            if selector.persist_selectee:
                ind = 0
            else:
                ind = 1
        else:
            if selectee.persist_selectee:
                ind = 0
            else:
                ind = 1
        if covert_move_on == True and ((adjoin == False and not (not selectee.persist_selectee and re.search('\w+~', selectee.head_chain.features[1]))) or (adjoin and not (not selector.persist_selectee and re.search('\w+~', selector.head_chain.features[1])))):
            found_overt_only_feature = False
            if not adjoin:
                features_to_search = selectee.head_chain.features[ind:]
            else:
                features_to_search = selector.head_chain.features[ind:]
            for feature in features_to_search:
                #certain licensees are barred from triggering covert movement..except in cases of pied-piping where the selector has the same feature somewhere in its feature sequence..
                if feature.lower() in overt_only_movers and (adjoin or (feature.lower() not in selector.head_chain.features and feature.upper() not in selector.head_chain.features)):
                    found_overt_only_feature = True
                    break
            if not found_overt_only_feature:
                mother_w_covert_mover = copy_expression(mother)
                if not adjoin:
                    mother_w_covert_mover.head_chain.inside_cost += selectee.head_chain.inside_cost
                else:
                    mother_w_covert_mover.head_chain.inside_cost += selector.head_chain.inside_cost
            else:
                mother_w_covert_mover = None
        else:
            mother_w_covert_mover = None
        pf_chain = None
        #if the selectee (selector in the adjunction case) has a x~ feature (a rightward movement, pf feature), then where covert movement takes place we
        #will need to keep a separate pf chain with the string/span and x~ feature, and delete the x~ feature from the lf (covert) chain.. this is to allow
        #for the scenario where, e.g., an object checks case covertly and is rightward moved.. it should move to the right from the position it was
        #in immediately prior to its first covert movement, not from the covert landing site since the pf features never reached this position.
        #of course, the mover must have at least two movement features (a leftward and a rightward) for this to apply..
        if mother_w_covert_mover != None:
            if (not adjoin and len(selectee.head_chain.features) > 2) or (adjoin and len(selector.head_chain.features) > 2):
                if adjoin == False:
                    target = selectee
                else:
                    target = selector
                for i in range(len(target.head_chain.features)):
                    if re.search('\w+~', target.head_chain.features[i]):
                        pf_chain = copy_chain(target.head_chain)
                        pf_chain.covert = False
                        pf_chain.features = [target.head_chain.features[i]]
                        pf_chain.subcatAgreeFeatures = [target.head_chain.subcatAgreeFeatures[i]]
                        pf_feature_index = i
                        #we have to delete x~ from selectee, but this must be done below once we have copied the selectee, rather than operating on the original
                        #hence we record the position of this feature in pf_feature_index
        found_covert_only_mover = False
        if direction == 'right' and adjoin == False:
            if mother.sc not in ["::", ":\u0305:\u0305"]:
                #only complements and adjuncts may adjoin to the right, not spec..
                if resultsExpressionList != None:
                    failure_messages.append("Rightward specifiers are disallowed.")
                return
            if not selectee.persist_selectee:
                features_to_search = selectee.head_chain.features[1:]
                #if it's a persistent selectee, then its next movement feature is D which is overt only, hence we don't do the check for covert only movers
                if features_to_search[0].lower() in covert_only_movers:
                    found_covert_only_mover = True
            if found_covert_only_mover:
                mother = None
            else:
                #put a trace in as the complement yield with variable span positions and unify mother's narrow yield span with that of
                #the trace complement - not the overt complement this time, which is moving! But overt complement in covert movement
                #version of mother - just the phonetics, the chain with features will remain separate..unless rightward movement is due to take place
                #in which case we still insert a trace and keep separate lf and pf chains..
                if fuse_dependents(mother.head_chain.string.l_dependent_yields, mother.head_chain.string.r_dependent_yields, check_dir = 'right', mother = mother) == False:
                    if resultsExpressionList != None:
                        failure_messages.append("String adjacency check failure for attempted merger of complement.")
                    mother = None
            if covert_move_on == True:
                if mother_w_covert_mover != None:
                    if pf_chain == None:
                        mother_w_covert_mover.head_chain.string.r_dependent_yields.append(Yield(fused_string, fused_span))
                    if fuse_dependents(mother_w_covert_mover.head_chain.string.l_dependent_yields, mother_w_covert_mover.head_chain.string.r_dependent_yields, check_dir = 'right', mother = mother_w_covert_mover) == False:
                        if resultsExpressionList != None:
                            failure_messages.append("String adjacency check failure for attempted merger of complement.")
                        mother_w_covert_mover = None
                    elif pf_chain == None:
                        mother_w_covert_mover.head_chain.string.narrow_yield.set_span(fused_span)
        elif direction == 'right' and adjoin == True:
            features_to_search = selector.head_chain.features[1:]
            #if it's a persistent selectee, then its next movement feature is D which is overt only, hence we don't do the check for covert only movers
            if features_to_search[0].lower() in covert_only_movers:
                found_covert_only_mover = True
            if found_covert_only_mover:
                mother = None
            else:#first we need to create the adjunct..
                if fuse_dependents(mother.head_chain.string.l_dependent_yields, mother.head_chain.string.r_dependent_yields, check_dir = 'left', mother = mother) == False:
                    if resultsExpressionList != None:
                        failure_messages.append("String adjacency check failure for attempted merger of adjunct.")
                    mother = None
                #if mother's narrow yield is [] or [[], []] we will unify it with the adjunct's (in case it is overt, quicker to not check) otherwise we leave it alone.
                elif mother.head_chain.string.narrow_yield.get_span() == [[], []]:
                    span = mother.head_chain.string.l_dependent_yields[0].get_span()
                    mother.head_chain.string.narrow_yield.set_span(span)
            if covert_move_on == True:
                if mother_w_covert_mover != None:
                    if pf_chain == None:
                        mother_w_covert_mover.head_chain.string.l_dependent_yields.insert(0, Yield(fused_string, fused_span))
                    if fuse_dependents(mother_w_covert_mover.head_chain.string.l_dependent_yields, mother_w_covert_mover.head_chain.string.r_dependent_yields, check_dir = 'left', mother = mother_w_covert_mover) == False:
                        if resultsExpressionList != None:
                            failure_messages.append("String adjacency check failure for attempted merger of adjunct.")
                        mother_w_covert_mover = None
                    else:
                        (left_pos, right_pos) = find_narrow_yield(mother_w_covert_mover)
                        mother_w_covert_mover.head_chain.string.narrow_yield.set_span([left_pos, right_pos])
        elif direction == 'left' and adjoin == True:
            features_to_search = selector.head_chain.features[1:]
            #if it's a persistent selectee, then its next movement feature is D which is overt only, hence we don't do the check for covert only movers
            if features_to_search[0].lower() in covert_only_movers:
                found_covert_only_mover = True
            if found_covert_only_mover:
                mother = None
            else:
                if fuse_dependents(mother.head_chain.string.l_dependent_yields, mother.head_chain.string.r_dependent_yields, check_dir = 'right', mother = mother) == False:
                    if resultsExpressionList != None:
                        failure_messages.append("String adjacency check failure for attempted merger of adjunct.")
                    mother = None
                #if mother's narrow yield is [] or [[], []] we will unify it with the adjunct's otherwise we leave it alone.
                elif mother.head_chain.string.narrow_yield.get_span() == [[], []]:
                    span = mother.head_chain.string.r_dependent_yields[-1].get_span()
                    mother.head_chain.string.narrow_yield.set_span(span)
            if covert_move_on == True and mother_w_covert_mover != None:
                if pf_chain == None:
                    mother_w_covert_mover.head_chain.string.r_dependent_yields.append(Yield(fused_string, fused_span))
                if fuse_dependents(mother_w_covert_mover.head_chain.string.l_dependent_yields, mother_w_covert_mover.head_chain.string.r_dependent_yields, check_dir = 'right', mother = mother_w_covert_mover) == False:
                    if resultsExpressionList != None:
                        failure_messages.append("String adjacency check failure for attempted merger of adjunct.")
                    mother_w_covert_mover = None
                else:
                    (left_pos, right_pos) = find_narrow_yield(mother_w_covert_mover)
                    mother_w_covert_mover.head_chain.string.narrow_yield.set_span([left_pos, right_pos])
        elif mother.sc in ['::', ':\u0305:\u0305']:
            if not selectee.persist_selectee:
                features_to_search = selectee.head_chain.features[1:]
                #if it's a persistent selectee, then its next movement feature is D which is overt only, hence we don't do the check for covert only movers
                if features_to_search[0].lower() in covert_only_movers:
                    found_covert_only_mover = True
            if found_covert_only_mover:
                mother = None
            else:
                if fuse_dependents(mother.head_chain.string.l_dependent_yields, mother.head_chain.string.r_dependent_yields, check_dir = 'left', mother = mother) == False:
                    if resultsExpressionList != None:
                        failure_messages.append("String adjacency check failure for attempted merger of complement.")
                    mother = None
                else:
                    mother.head_chain.string.narrow_yield.set_span(fused_span)
            if covert_move_on and mother_w_covert_mover != None:
                if pf_chain == None:
                    mother_w_covert_mover.head_chain.string.l_dependent_yields.insert(0, Yield(fused_string, fused_span))
                if fuse_dependents(mother_w_covert_mover.head_chain.string.l_dependent_yields, mother_w_covert_mover.head_chain.string.r_dependent_yields, check_dir = 'left', mother = mother_w_covert_mover) == False:
                    if resultsExpressionList != None:
                        failure_messages.append("String adjacency check failure for attempted merger of complement.")
                    mother_w_covert_mover = None
                elif pf_chain == None:
                    mother_w_covert_mover.head_chain.string.narrow_yield.set_span(fused_span)
        else:
            #this is a left merged specifier..
            if not selectee.persist_selectee:
                features_to_search = selectee.head_chain.features[1:]
                #if it's a persistent selectee, then its next movement feature is D which is overt only, hence we don't do the check for covert only movers
                if features_to_search[0].lower() in covert_only_movers:
                    found_covert_only_mover = True
            if found_covert_only_mover:
                mother = None
            else:
                #we unify mother's narrow yield with that of the specifier's ONLY if mother has no existing narrow yield
                if fuse_dependents(mother.head_chain.string.l_dependent_yields, mother.head_chain.string.r_dependent_yields, check_dir = 'left', mother = mother) == False:
                    if resultsExpressionList != None:
                        failure_messages.append("String adjacency check failure for attempted merger of specifier.")
                    mother = None
                elif mother.head_chain.string.narrow_yield.get_span() == [[], []]:
                    span = mother.head_chain.string.l_dependent_yields[0].get_span()
                    mother.head_chain.string.narrow_yield.set_span(span)
            if covert_move_on == True and mother_w_covert_mover != None:
                if pf_chain == None:
                    mother_w_covert_mover.head_chain.string.l_dependent_yields.insert(0, Yield(fused_string, fused_span))
                if fuse_dependents(mother_w_covert_mover.head_chain.string.l_dependent_yields, mother_w_covert_mover.head_chain.string.r_dependent_yields, check_dir = 'left', mother = mother_w_covert_mover) == False:
                    if resultsExpressionList != None:
                        failure_messages.append("String adjacency check failure for attempted merger of specifier.")
                    mother_w_covert_mover = None
                else:
                    (left_pos, right_pos) = find_narrow_yield(mother_w_covert_mover)
                    mother_w_covert_mover.head_chain.string.narrow_yield.set_span([left_pos, right_pos])
        #delete selector feature in mother, unless this is an adjunct, in which case, mother's features are the selectees
        #and adjunction feature checking is asymmetric
        #append all chains of the selectee, including its head chain since this time there are unchecked licensee features
        #and replace the selectee's head chain inside mother with the fused version since head movement from
        #the selectee is now impossible.. if this is adjunction, simply append the head chain of selector with the first feature deleted
        if adjoin == False:
            if mother != None:
                mother.head_chain.checked_features.append(mother.head_chain.features[0])
                del(mother.head_chain.features[0])
                del(mother.head_chain.subcatAgreeFeatures[0])
                selectee_head_chain_copy = copy_chain(selectee.head_chain)
                if hm_dir != None:
                    selectee_head_chain_copy.string.head_yield.remove(selectee_head_chain_copy.string.head_yield[-1])
                #since the selectee's head can now never undergo head movement, we fuse the selectees narrow yield as before..
                selectee_head_chain_copy.string.narrow_yield.set_yield(fused_string, fused_span)
                #if penn treebank spans are available, we now immediately test to see if this mover is a
                #constituent in the PTB and if it's not throw it out
                if moveable_spans != None:
                    selectee_span = selectee_head_chain_copy.string.narrow_yield.get_span()
                    if not (selectee_head_chain_copy.head_string in ['[wh]', '[relativizer]'] or selectee_span == [[],[]] or selectee_span in moveable_spans):
                        if resultsExpressionList != None:
                            failure_messages.append("PTB moveable spans do not match with a constituent you want to move!")
                        mother = None
                if mother != None:
                    #the covert moving copy just has variables for its narrow yield and an empty string
                    #we only delete the first feature of selectee if the latter tests false for .persist_selectee
                    if selectee.persist_selectee == False:
                        selectee_head_chain_copy.checked_features.append(selectee_head_chain_copy.features[0])
                        del(selectee_head_chain_copy.features[0])
                        del(selectee_head_chain_copy.subcatAgreeFeatures[0])
                    if selectee.persist_selectee:
                        for feature in suppressed_subcats:
                            if feature[1:] in selectee_head_chain_copy.subcatAgreeFeatures[0]:
                                selectee_head_chain_copy.subcatAgreeFeatures[0].remove(feature[1:])
                    mother.non_head_chains.append(selectee_head_chain_copy)
                    if ignore_dependent_chains == False:
                        for chain in selectee.non_head_chains:
                            chain_copy = copy_chain(chain)
                            mother.non_head_chains.append(chain_copy)
                    if direction == 'right':
                        mother.pointers.append(({'split':False, 'lex_head_coord':selectee.saturated and not adjoin, 'operation':'merge', 'phonetic_merge':False, 'adjoin':adjoin, 'hm_dir':hm_dir, 'direction':direction, 'persist_selectee':selectee.persist_selectee, 'ATB_drop':ATB_drop, 'persist_selector':False, 'escape':escape}, selector, selectee))
                    elif direction == 'left':
                        mother.pointers.append(({'split':False, 'lex_head_coord':selectee.saturated and not adjoin, 'operation':'merge', 'phonetic_merge':False, 'adjoin':adjoin, 'hm_dir':hm_dir, 'direction':direction, 'persist_selectee':selectee.persist_selectee, 'ATB_drop':ATB_drop, 'persist_selector':False, 'escape':escape}, selectee, selector))
            if mother_w_covert_mover != None:
                mother_w_covert_mover.head_chain.checked_features.append(mother_w_covert_mover.head_chain.features[0])
                del(mother_w_covert_mover.head_chain.features[0])
                del(mother_w_covert_mover.head_chain.subcatAgreeFeatures[0])
                covert_selectee_head_chain_copy = copy_chain(selectee.head_chain)
                covert_selectee_head_chain_copy.covert = True
                if hm_dir != None:
                    covert_selectee_head_chain_copy.string.head_yield.remove(covert_selectee_head_chain_copy.string.head_yield[-1])
                #since the selectee's head can now never undergo head movement, we fuse the selectees narrow yield as before..
                #the covert moving copy just has variables for its narrow yield and an empty string, but if there's a pf chain this
                #must be fused in the usual manner
                if pf_chain != None:
                    pf_chain.string.narrow_yield.set_yield(fused_string, fused_span)
                    del(covert_selectee_head_chain_copy.features[pf_feature_index])
                    del(covert_selectee_head_chain_copy.subcatAgreeFeatures[pf_feature_index])
                covert_selectee_head_chain_copy.string.narrow_yield.set_yield("", [[], []])
                if selectee.persist_selectee == False:
                    covert_selectee_head_chain_copy.checked_features.append(covert_selectee_head_chain_copy.features[0])
                    del(covert_selectee_head_chain_copy.features[0])
                    del(covert_selectee_head_chain_copy.subcatAgreeFeatures[0])
                else:
                    for feature in suppressed_subcats:
                        if feature[1:] in covert_selectee_head_chain_copy.subcatAgreeFeatures[0]:
                            covert_selectee_head_chain_copy.subcatAgreeFeatures[0].remove(feature[1:])
                mother_w_covert_mover.non_head_chains.append(covert_selectee_head_chain_copy)
                if pf_chain != None:
                    #if penn treebank spans are available, we now immediately test to see if this mover is a
                    #constituent in the PTB and if it's not throw it out
                    if moveable_spans != None:
                        pf_chain_span = pf_chain.string.narrow_yield.get_span()
                        if not (pf_chain.head_string in ['[wh]', '[relativizer]'] or pf_chain_span == [[],[]] or pf_chain_span in moveable_spans):
                            if resultsExpressionList != None:
                                failure_messages.append("PTB moveable spans do not match with a constituent you want to move!")
                            mother_w_covert_mover = None
                    if mother_w_covert_mover != None:
                        mother_w_covert_mover.non_head_chains.append(pf_chain)
                if mother_w_covert_mover != None:
                    if ignore_dependent_chains == False:
                        for chain in selectee.non_head_chains:
                            chain_copy = copy_chain(chain)
                            mother_w_covert_mover.non_head_chains.append(chain_copy)
                    if pf_chain == None:
                        if direction == 'right':
                            mother_w_covert_mover.pointers.append(({'split':False, 'lex_head_coord':selectee.saturated and not adjoin, 'operation':'merge', 'phonetic_merge':True, 'adjoin':adjoin, 'hm_dir':hm_dir, 'direction':direction, 'persist_selectee':selectee.persist_selectee, 'ATB_drop':ATB_drop, 'persist_selector':False, 'escape':escape}, selector, selectee))
                        else:
                            mother_w_covert_mover.pointers.append(({'split':False, 'lex_head_coord':selectee.saturated and not adjoin, 'operation':'merge', 'phonetic_merge':True, 'adjoin':adjoin, 'hm_dir':hm_dir, 'direction':direction, 'persist_selectee':selectee.persist_selectee, 'ATB_drop':ATB_drop, 'persist_selector':False, 'escape':escape}, selectee, selector))
                    else:
                        if direction == 'right':
                            mother_w_covert_mover.pointers.append(({'split':True, 'lex_head_coord':selectee.saturated and not adjoin, 'operation':'merge', 'phonetic_merge':False, 'adjoin':adjoin, 'hm_dir':hm_dir, 'direction':direction, 'persist_selectee':selectee.persist_selectee, 'ATB_drop':ATB_drop, 'persist_selector':False, 'escape':escape}, selector, selectee))
                        else:
                            mother_w_covert_mover.pointers.append(({'split':True, 'lex_head_coord':selectee.saturated and not adjoin, 'operation':'merge', 'phonetic_merge':False, 'adjoin':adjoin, 'hm_dir':hm_dir, 'direction':direction, 'persist_selectee':selectee.persist_selectee, 'ATB_drop':ATB_drop, 'persist_selector':False, 'escape':escape}, selectee, selector))
        else:
            if mother != None:
                selector_head_chain_copy = copy_chain(selector.head_chain)
                selector_head_chain_copy.checked_features.append(selector_head_chain_copy.features[0])
                del(selector_head_chain_copy.features[0])
                del(selector_head_chain_copy.subcatAgreeFeatures[0])
                #since the selector's head can now never undergo head movement, we fuse the selectors narrow yield as before..
                selector_head_chain_copy.string.narrow_yield.set_yield(fused_string, fused_span)
                #if penn treebank spans are available, we now immediately test to see if this mover is a
                #constituent in the PTB and if it's not throw it out
                if moveable_spans != None:
                    selector_span = selector_head_chain_copy.string.narrow_yield.get_span()
                    if not (selector_head_chain_copy.head_string in ['[wh]', '[relativizer]'] or selector_span == [[],[]] or selector_span in moveable_spans or selector):
                        if resultsExpressionList != None:
                            failure_messages.append("PTB moveable spans do not match with a constituent you want to move!")
                        mother = None
                if mother != None:
                    mother.non_head_chains.append(selector_head_chain_copy)
                    if ignore_dependent_chains == False:
                        #any movers inside the adjunct exempted from CED are now transferred into mother
                        for chain in selector.non_head_chains:
                            chain_copy = copy_chain(chain)
                            mother.non_head_chains.append(chain_copy)
                    if direction == 'right':
                        mother.pointers.append(({'split':False, 'lex_head_coord':selectee.saturated and not adjoin, 'operation':'merge', 'phonetic_merge':False, 'adjoin':adjoin, 'hm_dir':hm_dir, 'direction':direction, 'persist_selectee':False, 'ATB_drop':ATB_drop, 'persist_selector':False, 'escape':escape}, selector, selectee))
                    else:
                        mother.pointers.append(({'split':False, 'lex_head_coord':selectee.saturated and not adjoin, 'operation':'merge', 'phonetic_merge':False, 'adjoin':adjoin, 'hm_dir':hm_dir, 'direction':direction, 'persist_selectee':False, 'ATB_drop':ATB_drop, 'persist_selector':False, 'escape':escape}, selectee, selector))
            if mother_w_covert_mover != None:
                covert_selector_head_chain_copy = copy_chain(selector.head_chain)
                covert_selector_head_chain_copy.covert = True
                if pf_chain != None:
                    pf_chain.string.narrow_yield.set_yield(fused_string, fused_span)
                    del(covert_selector_head_chain_copy.features[pf_feature_index])#added in covert_ 27th jan, hoep this was right
                    del(covert_selector_head_chain_copy.subcatAgreeFeatures[pf_feature_index])
                covert_selector_head_chain_copy.checked_features.append(covert_selector_head_chain_copy.features[0])
                del(covert_selector_head_chain_copy.features[0])
                del(covert_selector_head_chain_copy.subcatAgreeFeatures[0])
                #since the selector's head can now never undergo head movement, we fuse the selectors narrow yield as before..
                covert_selector_head_chain_copy.string.narrow_yield.set_yield("", [[], []])
                mother_w_covert_mover.non_head_chains.append(covert_selector_head_chain_copy)
                if pf_chain != None:
                    #if penn treebank spans are available, we now immediately test to see if this mover is a
                    #constituent in the PTB and if it's not throw it out
                    if moveable_spans != None:
                        pf_chain_span = pf_chain.string.narrow_yield.get_span()
                        if not (pf_chain.head_string in ['[wh]', '[relativizer]'] or pf_chain_span == [[],[]] or pf_chain_span in moveable_spans):
                            if resultsExpressionList != None:
                                failure_messages.append("PTB moveable spans do not match with a constituent you want to move!")
                            mother_w_covert_mover = None
                    if mother_w_covert_mover != None:
                        mother_w_covert_mover.non_head_chains.append(pf_chain)
                        if ignore_dependent_chains == False:
                            #any movers inside the adjunct exempted from CED are now transferred into mother
                            for chain in selector.non_head_chains:
                                chain_copy = copy_chain(chain)
                                mother.non_head_chains.append(chain_copy)
                if mother_w_covert_mover != None:
                    if pf_chain == None:
                        if direction == 'right':
                            mother_w_covert_mover.pointers.append(({'split':False, 'lex_head_coord':selectee.saturated and not adjoin, 'operation':'merge', 'phonetic_merge':True, 'adjoin':adjoin, 'hm_dir':hm_dir, 'direction':direction, 'persist_selectee':False, 'ATB_drop':ATB_drop, 'persist_selector':False, 'escape':escape}, selector, selectee))
                        else:
                            mother_w_covert_mover.pointers.append(({'split':False, 'lex_head_coord':selectee.saturated and not adjoin, 'operation':'merge', 'phonetic_merge':True, 'adjoin':adjoin, 'hm_dir':hm_dir, 'direction':direction, 'persist_selectee':False, 'ATB_drop':ATB_drop, 'persist_selector':False, 'escape':escape}, selectee, selector))
                    else:
                        #if we split the chain up into semantic and phonetic parts then this isn't phon merge as no phonetics are
                        #actually being merged with the governor
                        if direction == 'right':
                            mother_w_covert_mover.pointers.append(({'split':True, 'lex_head_coord':selectee.saturated and not adjoin, 'operation':'merge', 'phonetic_merge':False, 'adjoin':adjoin, 'hm_dir':hm_dir, 'direction':direction, 'persist_selectee':False, 'ATB_drop':ATB_drop, 'persist_selector':False, 'escape':escape}, selector, selectee))
                        else:
                            mother_w_covert_mover.pointers.append(({'split':True, 'lex_head_coord':selectee.saturated and not adjoin, 'operation':'merge', 'phonetic_merge':False, 'adjoin':adjoin, 'hm_dir':hm_dir, 'direction':direction, 'persist_selectee':False, 'ATB_drop':ATB_drop, 'persist_selector':False, 'escape':escape}, selectee, selector))
        if mother != None:
            if variable_found:
                for item in mother.head_chain.subcatAgreeFeatures:
                    if variable in item:
                        item.remove(variable)
            if mother.sc in [':\u0305', ':\u0305:\u0305']:
                mother.sc = ':\u0305'
            else:
                mother.sc = ':'
            mother.non_head_chains = sorted(mother.non_head_chains, key=lambda x: x.string.narrow_yield.span)
            if resultsExpressionList == None:
                add_to_agenda(item = mother, agenda = agenda, sentence_length = sentence_length, merge_arg1=selector, merge_arg2=selectee, printPartialAnalyses=printPartialAnalyses)
            else:
                resultsExpressionList.append(mother)
        if mother_w_covert_mover != None:
            if variable_found:
                for item in mother_w_covert_mover.head_chain.subcatAgreeFeatures:
                    if variable in item:
                        item.remove(variable)
            if mother_w_covert_mover.sc in [':\u0305', ':\u0305:\u0305']:
                mother_w_covert_mover.sc = ':\u0305'
            else:
                mother_w_covert_mover.sc = ':'
            mother_w_covert_mover.non_head_chains = sorted(mother_w_covert_mover.non_head_chains, key=lambda x: x.string.narrow_yield.span)
            if resultsExpressionList == None:
                add_to_agenda(item = mother_w_covert_mover, agenda = agenda, sentence_length = sentence_length, merge_arg1=selector, merge_arg2=selectee, printPartialAnalyses=printPartialAnalyses)
            else:
                resultsExpressionList.append(mother_w_covert_mover)
        return

def find_narrow_yield(mother):
    #returns the narrow yield span of an expression
    left_pos = None
    right_pos = None
    for PART in mother.head_chain.string.narrow_yield.get_string():
        if PART != mother.head_chain.string.head_yield:
            for part in PART:
                span = part.get_span()
                if span != [] and span != [[], []]:
                    if left_pos == None:
                    #for left we just take the first non null position we see,
                    #for right we keep resetting it till the end of the list when we will have the rightmost
                    #constituent (in the list, the spans may be wrong but that will be caught when this mother is
                    #merged as a dependent..
                        left_pos = span[0]
                    right_pos = span[1]
    if [left_pos, right_pos] != [None, None]:
        return (left_pos, right_pos)
    else:
        return (mother.head_chain.string.narrow_yield.get_span())

def copy_chain(chain):
    chain_copy = copy.deepcopy(chain)
    #we need to make sure that position variables are not deepcopied..
    ns = chain.string.narrow_yield.get_span()
    if ns == [[], []]:
        chain_copy.string.narrow_yield.set_span(ns)
    for i in range(len(chain.string.l_dependent_yields)):
        if chain.string.l_dependent_yields[i].get_span() == [[], []]:
            chain_copy.string.l_dependent_yields[i].set_span(chain.string.l_dependent_yields[i].get_span())
    for i in range(len(chain.string.head_yield)):
        if chain.string.head_yield[i].get_span() == [[], []]:
            chain_copy.string.head_yield[i].set_span(chain.string.head_yield[i].get_span())
    for i in range(len(chain.string.r_dependent_yields)):
        if chain.string.r_dependent_yields[i].get_span() == [[], []]:
            chain_copy.string.r_dependent_yields[i].set_span(chain.string.r_dependent_yields[i].get_span())
    return chain_copy

def copy_expression(exp):
    #we need to preserve all position variables [] inside any copied expressions..
    #pointers are not copied here as very often a copy of the head child serves as a starting point for the mother node
    exp_copy = Expression()
    exp_copy.ID = exp.ID
    exp_copy.inside_cost = exp.inside_cost
    exp_copy.outside_cost = exp.outside_cost
    exp_copy.total_cost = exp.total_cost
    exp_copy.cat_feature = exp.cat_feature
    exp_copy.head_string = exp.head_string
    exp_copy.is_overt = exp.is_overt
    exp_copy.sc = exp.sc
    exp_copy.head_chain = copy_chain(exp.head_chain)
    exp_copy.licensees = copy.deepcopy(exp.licensees)
    exp_copy.saturated = exp.saturated
    exp_copy.was_coordinator = exp.was_coordinator
    for i in range(len(exp.non_head_chains)):
        chain_copy = copy_chain(exp.non_head_chains[i])
        exp_copy.non_head_chains.append(chain_copy)
    exp_copy.exp_signature = exp.exp_signature
    return exp_copy

def add_to_chart(trigger_item, sentence_length, agenda, adjoin_or_coord_only=False, printPartialAnalyses=False):
    global chart_size
    #adds an item to the chart as long as it is not identical to an item already there
    #if this trigger item has no features, we can discard it
    global chart
    #we do the relativized smc check here, after any movement has taken place
    if smc_violation(trigger_item, relativized=True)[0]:
        return
    if len(trigger_item.head_chain.features) == 0:
        return
    (trigger_key, target_signs, trigger_cat) = get_keys(trigger_item)
    if trigger_item.head_chain.string.narrow_yield.get_span() != [[], []]:
        trigger_item_start = trigger_item.head_chain.string.narrow_yield.get_span()[0]#1
        trigger_item_end = trigger_item.head_chain.string.narrow_yield.get_span()[1]
    else:
        trigger_item_start = 0
        trigger_item_end = 0
    trigger_item.exp_signature = generate_exp_signature(trigger_item)
    if trigger_item.exp_signature in chart[trigger_item_start][trigger_item_end]['signatures']:
        #because this is astar, not cky, if there is already an item in the chart with the same signature
        #we don't add this item because the one in the chart must have better score.. in fact, this hsould never
        #happen here as we already checked the chart for duplicates in add_to_agenda()
        sys.stderr.write("\nOops, something is wrong, there should not be duplicates in the chart at this point!")
        return
    #we will store expressions in each cell as values in a python dictionary whose trigger_key is the GENERAL feature type (selector/selectee/
    #licensor/licensee) plus the category.. hence trigger_keys include =D, -v, C, +C etc but not D=, =D< etc
    if trigger_key not in chart[trigger_item_start][trigger_item_end]:
        chart[trigger_item_start][trigger_item_end][trigger_key] = []
    chart_size+=1
    if chart_size % 20000 == 0:
        sys.stderr.write("\nCurrent number of chart entries: "+str(chart_size))
    chart[trigger_item_start][trigger_item_end][trigger_key].append(trigger_item)
    chart[trigger_item_start][trigger_item_end]['signatures'][trigger_item.exp_signature] = [trigger_item]
    for target_sign in target_signs:
        target_key=target_sign+trigger_cat
        generate_new_expressions(trigger_item = trigger_item, agenda = agenda, sentence_length = sentence_length, trigger_key = trigger_key, target_key = target_key, adjoin_or_coord_only=adjoin_or_coord_only, printPartialAnalyses=printPartialAnalyses)

def generate_exp_signature(trigger_item):
    sig = ""
    if trigger_item.persist_selectee:
        sig+="PS "
    if trigger_item.was_coordinator:
        sig+="WC "
    if trigger_item.saturated:
        sig+="SAT "
    if trigger_item.head_chain.string.l_dependent_yields != []:
        l_span = trigger_item.head_chain.string.l_dependent_yields[0].get_span()
        if l_span != [[],[]]:
            sig += str(l_span)+"; "
        else:
            sig += u'\u03b5'+'; '
    else:
        sig += u'\u03b5'+'; '
    h_span = trigger_item.head_chain.string.head_yield[0].get_span()
    h_string = trigger_item.head_chain.string.head_yield[0].get_string()
    if h_span != [[],[]]:
        sig += str(trigger_item.head_chain.string.head_yield[0].get_span())+"; "
    else:
        if trigger_item.pointers != []:
            sig += u'\u03b5'+'; '
        else:
            sig += h_string+"; "
    if trigger_item.head_chain.string.r_dependent_yields != []:
        r_span = trigger_item.head_chain.string.r_dependent_yields[0].get_span()
        if r_span != [[],[]]:
            sig += str(trigger_item.head_chain.string.r_dependent_yields[0].get_span())+" "
        else:
            sig += u'\u03b5'+' '
    else:
        sig += u'\u03b5'+' '
    sig+=trigger_item.sc+" "
    f_index = -1
    len_checked = len(trigger_item.head_chain.checked_features)
    for feature in trigger_item.head_chain.features:
        f_index+=1
        if len(trigger_item.head_chain.subcatAgreeFeatures[f_index]) > 0:
            if trigger_item.ID in supertag_links:
                cf_index = str(f_index + len_checked)
                if cf_index in supertag_links[trigger_item.ID]:
                    sig+=(feature+"{"+".".join(trigger_item.head_chain.subcatAgreeFeatures[f_index])+"}^"+supertag_links[trigger_item.ID][cf_index]+" ").decode('utf8')
                else:
                    sig+=(feature+"{"+".".join(trigger_item.head_chain.subcatAgreeFeatures[f_index])+"} ").decode('utf8')
            else:
                sig+=(feature+"{"+".".join(trigger_item.head_chain.subcatAgreeFeatures[f_index])+"} ").decode('utf8')
        else:
            if trigger_item.ID in supertag_links:
                cf_index = str(f_index + len_checked)
                if cf_index in supertag_links[trigger_item.ID]:
                    sig+=(feature+"^"+supertag_links[trigger_item.ID][cf_index]+" ").decode('utf8')
                else:
                    sig+=(feature+" ").decode('utf8')
            else:
                sig+=(feature+" ").decode('utf8')
    sig=sig.strip()
    for chain in trigger_item.non_head_chains:
        sig += ", "
        if chain.covert:
            sig += "CV "
        if chain.overt_movement_required:
            sig += "OMR"
        chain_yield = chain.string.narrow_yield.get_span()
        if chain_yield != [[],[]]:
            sig += str(chain_yield)
        else:
            sig += u'\u03b5'
        sig += " "+chain.sc+" "
        if chain.checked_features != [] and chain.checked_features[-1] in ['-NOM', '-ACC', '-GEN', '-DAT']:
            sig+=chain.checked_features[-1]+" . "
        f_index = -1
        for feature in chain.features:
            f_index+=1
            if len(chain.subcatAgreeFeatures[f_index]) > 0:
                sig+=(feature+"{"+".".join(chain.subcatAgreeFeatures[f_index])+"} ").decode('utf8')
            else:
                sig+=(feature+" ").decode('utf8')
        sig=sig.strip()
    return sig

def multiple_rel_violation(trigger_item):
    #we ban more than one moving chain having either a [wh]
    #or [relativizer] headed constituent as this improves efficiency
    #and there is never any need more more than one of these (overt wh
    #is allowed, since here we must allow the wh element to separate from
    #the relativized element).
    relative_count = 0
    for chain in trigger_item.non_head_chains:
        if chain.head_string == '[relativizer]' or chain.head_string == '[wh]':
            relative_count += 1
        if relative_count > 1:
            return True
    return False

def get_keys(trigger_item):
    #returns the keys which are used to match items in the chart - items are listed there according to
    #their first feature, in order to save searching every item in each cell
    cat = re.compile('\w+')
    f_type = re.compile('[=+-]')
    #for some reason, putting the approximately equal to sign in the [] breaks the system
    f_adjunct_type = re.compile('≈')
    trigger_cat = cat.search(trigger_item.head_chain.features[0])
    trigger_type = f_type.search(trigger_item.head_chain.features[0])
    trigger_type_adjunct = f_adjunct_type.search(trigger_item.head_chain.features[0])
    if trigger_type:
        trigger_key = trigger_type.group(0)+trigger_cat.group(0)
        trigger_type = trigger_type.group(0)
    elif trigger_type_adjunct:
        trigger_key = trigger_type_adjunct.group(0)+trigger_cat.group(0)
        trigger_type = trigger_type_adjunct.group(0)
    else:
        #for selectee features which lack =/+/-/≈
        trigger_key = trigger_cat.group(0)
        trigger_type = ''
    target_signs = feature_mapping[trigger_type]
    return (trigger_key.lower(), target_signs, trigger_cat.group(0).lower())

def expressions_identical(trigger_item, expression, check_ids=True, check_head_string=False):
    #THIS FUNCTION IS COMPUTATIONALLY COSTLY!  ONLY USE WHERE ABSOLUTELY NECESSARY!
    #compares two expressions and returns True if they are identical (including their pointers) to avoid duplicates in the chart
    #but before the duplicate is thrown away, it's pointers are entered into the already existing entry
    #if they are unique
    if check_head_string:
        if trigger_item.head_string != expression.head_string:
            return False
    if check_ids:
        if trigger_item.ID != expression.ID:
            return False
    if trigger_item.exp_signature != expression.exp_signature:
        return False
    if not chains_identical(trigger_item.head_chain, expression.head_chain):
        return False
    for i in range(len(trigger_item.non_head_chains)):
        if not chains_identical(trigger_item.non_head_chains[i], expression.non_head_chains[i]):
            return False
    return True

def chains_identical(chain1, chain2):
    #compares two chains to see if their features and the spans of their spec-head-comps are identical
    #we don't need to worry about constituents whose spec-head-comp spans have been fused because these
    #will never be entered into the chart anyway since all they can do is move, which is a unary operation
    #we only need to check the most recently checked checked features for case conflicts.. otherwise they can differ..
    if not features_identical(chain1.features, chain2.features):
        return False
    if chain1.subcatAgreeFeatures != chain2.subcatAgreeFeatures:
        return False
    if case_conflict(chain1.checked_features, chain2.checked_features):
        return False
    else:
        if chain1.string.narrow_yield.get_span() != chain2.string.narrow_yield.get_span():
            return False
    return True

def features_identical(features1, features2):
    index = -1
    if len(features1) != len(features2):
        return False
    for feature in features1:
        index+=1
        if feature != features2[index]:
            return False
    return True

def case_conflict(checked_features1, checked_features2):
    #for purposes of ATB movement, the unified movers must not currently be sat in distict case positions.. this function checks that
    #-CASE is unvalued case and cannot be judged as distinct from any valued case
    if len(checked_features1) > 0 and len(checked_features2) > 0:
        if checked_features1[-1] in ['-ACC', '-NOM', '-GEN', '-DAT'] and checked_features2[-1] in ['-ACC', '-NOM', '-GEN', '-DAT']:
            if checked_features1[-1] != checked_features2[-1]:
                return True
    return False

def overlap(target_item, trigger_item):
    if re.search(left_merge_x_h_move, target_item.head_chain.features[0]) or re.search(left_merge_x_h_move, trigger_item.head_chain.features[0]):
        atb_head_drop = True
    else:
        atb_head_drop = False
    target_spans = []
    trigger_spans = []
    #we first construct a list of chains, omitting any chains in the target which are identical to a chain in the
    #trigger (to allow for ATB movement)..
    target_chains = []
    trigger_chains = []
    for target_chain in target_item.non_head_chains:
        omit_chain = False
        for trigger_chain in trigger_item.non_head_chains:
           if chains_identical(target_chain, trigger_chain):
               omit_chain = True
               break
        if omit_chain == False:
            target_chains.append(target_chain)
    for trigger_chain in trigger_item.non_head_chains:
        omit_chain = False
        for target_chain in target_item.non_head_chains:
           if chains_identical(target_chain, trigger_chain):
               omit_chain = True
               break
        if omit_chain == False:
            trigger_chains.append(trigger_chain)
    target_spans += [YIELD.get_span() for YIELD in target_item.head_chain.string.l_dependent_yields]
    target_spans += [YIELD.get_span() for YIELD in target_item.head_chain.string.r_dependent_yields]
    target_spans += [YIELD.get_span() for YIELD in target_item.head_chain.string.head_yield]
    trigger_spans += [YIELD.get_span() for YIELD in trigger_item.head_chain.string.l_dependent_yields]
    trigger_spans += [YIELD.get_span() for YIELD in trigger_item.head_chain.string.r_dependent_yields]
    if not atb_head_drop:
        #if atb_head_drop is true then we don't want to abort just because the two head chains have the same
        #yield, so we ignore one of them (doesn't matter which one).. don't want to ignore both
        #as then we would not abort if one of the moving chains had the same span as the head word, which
        #would be incorrect..
        trigger_spans += [YIELD.get_span() for YIELD in trigger_item.head_chain.string.head_yield]
    #don't include the head yields in these checks because heads can move (doing so blocks the
    #atb head movement construction
    for chain in target_chains:
        target_spans.append(chain.string.narrow_yield.get_span())
    for chain in trigger_chains:
        trigger_spans.append(chain.string.narrow_yield.get_span())
    for target_span in target_spans:
        if target_span != [[], []]:
            for trigger_span in trigger_spans:
                if trigger_span != [[], []]:
                    if target_span[1] > trigger_span[0]:
                        if not (target_span[0] >= trigger_span[1]):
                            return True
                    if target_span[0] < trigger_span[1]:
                        if not (target_span[1] <= trigger_span[0]):
                            return True
                    if target_span[1] == trigger_span[0]:
                        if not (target_span[0] <= trigger_span[0]):
                            return True
                    if target_span[0] == trigger_span[1]:
                        if not (target_span[1] >= trigger_span[1]):
                            return True
    return False

def generate_new_expressions(trigger_item, agenda, sentence_length, trigger_key, target_key, adjoin_or_coord_only=False, printPartialAnalyses=False):
    #takes as input a trigger item from the agenda and tries merging it with all non-overlapping items
    #in the chart
    trigger_cat = None
    null_trigger = False
    if trigger_item.head_chain.string.narrow_yield.get_span() != [[], []]:
        trigger_item_start = trigger_item.head_chain.string.narrow_yield.get_span()[0]#2
        trigger_item_end = trigger_item.head_chain.string.narrow_yield.get_span()[1]
    else:
        trigger_item_start = 0
        trigger_item_end = 0
    if trigger_item_start == trigger_item_end == 0:
        null_trigger = True
    #try merging the trigger item with all constituents (not necessarily adjacent) to its left
    for i in range(trigger_item_start+1):
        for k in range(trigger_item_start+1):
            if not maxMoveDist == None and not ((i == k == 0) or null_trigger):
                if trigger_item_start - k > maxMoveDist:
                    continue
            try:
                for target_item in chart[i][k][target_key]:
                    if overlap(target_item, trigger_item) == True:
                        continue
                    merge(trigger_item = trigger_item, target_item = target_item, agenda = agenda, sentence_length = sentence_length, adjoin_or_coord_only=adjoin_or_coord_only, printPartialAnalyses=printPartialAnalyses)
            except KeyError:
                x=0
    #now try merging the trigger item with everything to its right
    for i in range((sentence_length - trigger_item_end)+1):
        for k in range((sentence_length - trigger_item_end)+1):
            #because target in 0,0 is handled above, we ignore it here
            if i == 0 and k == 0:
                continue
            if not maxMoveDist == None and not (((trigger_item_end+i) == (trigger_item_end+k) == 0) or null_trigger):
                if i > maxMoveDist:
                    continue
            try:
                for target_item in chart[trigger_item_end+i][trigger_item_end+k][target_key]:
                    if overlap(target_item, trigger_item) == True:
                        continue
                    merge(trigger_item = trigger_item, target_item = target_item, agenda = agenda, sentence_length = sentence_length, adjoin_or_coord_only=adjoin_or_coord_only, printPartialAnalyses=printPartialAnalyses)
            except KeyError:
                x=0

def add_to_agenda(item, agenda, sentence_length=None, returnToAutobank=False, failure_messages=None, move_arg=None, merge_arg1=None, merge_arg2=None, printPartialAnalyses=False):
    #adds an item to the agenda according to it's narrow yield but only if it is not in the chart (if its already in the agenda, but has a lower cost here, its score is updated)
    #, if it is in the agenda but not the chart, then if the new item has a lower cost we reorder the agenda according to the lower cost
    #and change the pointers of the item in the agenda to be the pointers of the new item
    if num_extraposers(item) > 2:
        return
    if multiple_rel_violation(item):
        return
    if smc_violation(item)[0]:
        return
    if item.head_chain.string.narrow_yield.get_span() != [[], []]:
        item_start = item.head_chain.string.narrow_yield.get_span()[0]
        item_end = item.head_chain.string.narrow_yield.get_span()[1]
    else:
        item_start = 0
        item_end = 0
    items = [item]
    if item.head_chain.features[0] == 'D':
        persistent_item = copy_expression(item)
        persistent_item.pointers = item.pointers
        persistent_item.persist_selectee = True
        items.append(persistent_item)
    for item in items:
        item.exp_signature = generate_exp_signature(item)
        if item.exp_signature in chart[item_start][item_end]['signatures']:
            #item.outside_cost = Decimal(chart[item_start][item_end]['signatures'][item.exp_signature][0].outside_cost)
            #item.total_cost = Decimal(item.inside_cost+item.outside_cost)
            #if chart[item_start][item_end]['signatures'][item.exp_signature][0].total_cost > item.total_cost:
                #print "Oops, there is an identical item already in the chart but with a higher cost!!!!"
            #if the item is already in the chart then the one in the chart must have a higher score so we just return
            return
        elif item.exp_signature in agenda_signatures:
            item.outside_cost = Decimal(agenda_signatures[item.exp_signature][0].outside_cost)
            item.total_cost = Decimal(item.inside_cost+item.outside_cost)
            if agenda_signatures[item.exp_signature][0].total_cost > item.total_cost:
                #if the item is not in the chart but is already in the agenda, we change the priority and pointers
                #of the one in the agenda to match the new one only if the new one has a lower cost
                agenda.decrease_key(agenda_signatures[item.exp_signature][1], item.total_cost)
                agenda_signatures[item.exp_signature][0].total_cost = item.total_cost
                agenda_signatures[item.exp_signature][0].inside_cost = item.inside_cost
                agenda_signatures[item.exp_signature][0].pointers = item.pointers
            return
        else:
            if item.outside_cost == None:
                item.outside_cost = Decimal(0)
                #if item.outside_cost == None then this item is new and is the result of merge, so we must calculate outside cost
                inside_yields = []
                head_yield = item.head_chain.string.head_yield[0].get_span()
                l_dependent_yield = item.head_chain.string.l_dependent_yields[0].get_span()
                r_dependent_yield = item.head_chain.string.r_dependent_yields[0].get_span()
                inside_yields.append(head_yield)
                inside_yields.append(l_dependent_yield)
                inside_yields.append(r_dependent_yield)
                for chain in item.non_head_chains:
                    inside_yields.append(chain.string.narrow_yield.get_span())
                while [[],[]] in inside_yields:#EDITremovall
                    inside_yields.remove([[],[]])
                outside_yields = get_outside_spans(inside_yields, sentence_length)
                for span in outside_yields:
                    item.outside_cost += Decimal(outside_costs[span])
                item.total_cost = Decimal(item.inside_cost+item.outside_cost)
            fib_heap_entry = agenda.enqueue(item, item.total_cost)           
            agenda_signatures[item.exp_signature] = [item, fib_heap_entry]
        if printPartialAnalyses:
            if move_arg != None:
                print "Move arg:"
                move_arg.print_exp()
                print "--------------------------------------------------------------------------------"
                print "Move result:"
                item.print_exp()
            else:
                print "Merge arg1:"
                merge_arg1.print_exp()
                print "--------------------------------------------------------------------------------"
                print "Merge arg2:"
                merge_arg2.print_exp()
                print "--------------------------------------------------------------------------------"
                print "Merge Result:"
                item.print_exp()
            print "********************************************************************************"
            print "********************************************************************************"

def get_outside_spans(inside_spans, sent_length):
    outside_spans = []
    position = 0
    for span in sorted(inside_spans):
        if span[0]-position>0:
            outside_spans.append( (position, span[0]) )
        position = span[1]
    if position < sent_length:
        outside_spans.append( (position, sent_length) )
    return outside_spans

def smc_violation(item, relativized=False, failure_messages=None):
    move_features = {}
    for chain in item.non_head_chains:
        if len(chain.string.head_yield) > 1:
            return (True, False)
        if chain.features[0].lower() in move_features:
            return (True, False)
        if relativized:
            #the following lines relativize the SMC to A-movement vs A'-movement features..
            #so there can, e.g. be only one A-movement feature in the tree at any one time..
            chain_features0_lower = chain.features[0].lower()
            if chain_features0_lower in multiple_agree_features:
                #phi features do not clash with one another for TSMC, but only two phi
                #features mary be active in the derivation at any one time
                phi = True
            else:
                phi = False
            if chain_features0_lower in A_features:
                if phi:
                    phi_count = 1
                m_index = -1
                for feature in move_features:
                    m_index += 1
                    if phi:
                        #for phi features, -pers, -num, -epp, these are used in constructions
                        #in which a DP has an associate, either empletive 'there', an inverted PP, or floating quantifier..
                        #there should therefore only ever be two multiple_agree_features active in the derivation at any one time.
                        if feature in multiple_agree_features:
                            phi_count += 1
                            if phi_count == 3:
                                return (True, True)
                    if (feature in A_features and not (phi and feature in multiple_agree_features)):
                        return (True, True)
            if chain_features0_lower in Abar_features:
                for feature in move_features:
                    if feature in Abar_features:
                        return (True, True)
            if chain_features0_lower in A2_features:
                if phi:
                    phi_count = 1
                for feature in move_features:
                    if phi:
                        if feature in multiple_agree_features:
                            phi_count += 1
                            if phi_count == 3:
                                return (True, True)
                    if feature in A2_features and not (phi and feature in multiple_agree_features):
                        return (True, True)
            if chain_features0_lower in Abar2_features:
                for feature in move_features:
                    if feature in Abar2_features:
                        return (True, True)
        move_features[chain.features[0].lower()] = 1
    return (False, False)

def num_extraposers(item):
    count = 0
    for feature in item.head_chain.features:
        if re.search('\w+~', feature):
            count += 1
    for chain in item.non_head_chains:
        for feature in chain.features:
            if re.search('\w+~', feature):
                count += 1
    return count

def astar_parse(args):
    supertagger = Supertagger.Supertagger(args.model_dir[0]+'/'+args.supertag_type[0]+'_model')
    tag_dict = json.load(open('./SuperSuperTagger/'+args.supertag_type[0]+'_data'+'/tag_dict'))
    seed_tag_dict = json.load(open('./SuperSuperTagger/'+args.supertag_type[0]+'_data'+'/seed_tag_dict'))
    input_file = open(args.input_file[0], 'r')
    parses = {}
    line_index = -1
    for line in input_file:
        line_index += 1
        sentence = word_tokenize(line)
        words_to_remove = []
        for i in range(len(sentence)):
            if sentence[i] in punctuation or sentence[i] == "''":
                words_to_remove.append(sentence[i])
        while len(words_to_remove) > 0:
            sentence.remove(words_to_remove[0])
            del(words_to_remove[0])
        for i in range(len(sentence)):
            sentence[i] = sentence[i].lower()
            try:
                float(sentence[i])
                sentence[i] = 'num'
            except ValueError:
                x=0
        sys.stderr.write('\nSupertagging sentence: '+(' ').join(sentence)+'\n')
        best_k = supertagger.bestK(sentence, args.k[0], aux_tags=None)
        sys.stderr.write('\nSupertagging successful..')
        best_k_file = open('best_k', 'w')
        for i in range(len(sentence)):
            best_k_file.write(sentence[i]+'\t'+'X'+'\t')
            for tag in best_k[i][:-1]:
                best_k_file.write(tag[0]+" "+str(tag[1])+'\t')
            best_k_file.write(best_k[i][-1][0]+" "+str(best_k[i][-1][1]))
            if i != len(sentence)-1:
                best_k_file.write('\n')
        best_k_file.close()
        best_k_file = open('best_k', 'r')
        REF_MGST_table = json.load(open('SuperSuperTagger/'+args.supertag_type[0]+'_data'+'/REF_MGST_table'))
        supertag_lists = []
        for line in best_k_file:
            supertag_list = [st for st in line.split('\t')[2:] if st[0] != '<' and line != '\n']
            if supertag_list == []:
                continue
            if supertag_list[-1][-1] == '\n':
                supertag_list[-1] = supertag_list[-1][:-1]
            supertag_lists.append(supertag_list)
        best_k_file.close()
        supertags = []
        for INDEX in range(len(sentence)):
            for supertag in supertag_lists[INDEX]:
                parts = supertag.split(' ')
                supertags.append([REF_MGST_table[parts[0]], float(parts[1]), INDEX])
        new_supertags = []
        word_tagged = {}
        for MGcat in supertags:
            MGcat = copy.deepcopy(MGcat)
            INDEX = MGcat[2]
            if INDEX not in word_tagged:
                word_tagged[INDEX] = False
            st = MGcat[0]
            if type(st[0][0][0]) != type([]) and type(st[0][0][0]) != type(()):
                if st[0][0] == 'OVERT_WORD':
                    overt_cat = copy.deepcopy(st)
                    st[0] = (sentence[INDEX], st[0][1], st[0][2])
                st[2] = INDEX
            else:
                for link in st:
                    if link[0][0][0] == 'OVERT_WORD':
                        overt_cat = copy.deepcopy(link[0])
                        link[0][0] = (sentence[INDEX], link[0][0][1], link[0][0][2])
                    if link[0][2] == None:
                        link[0][2] = INDEX
                    if link[2][0][0] == 'OVERT_WORD':
                        overt_cat = copy.deepcopy(link[2])
                        link[2][0] = (sentence[INDEX], link[2][0][1], link[2][0][2])
                    if link[2][2] == None:
                        link[2][2] = INDEX
            include_supertag = True
            seed_threshold_met = False
            if sentence[INDEX] in seed_tag_dict and seed_tag_dict[sentence[INDEX]][0] >= args.seed_tag_dict_min[0]:
                if overt_cat[0] not in seed_tag_dict[sentence[INDEX]]:
                    include_supertag = False
            if not seed_threshold_met and sentence[INDEX] in tag_dict and tag_dict[sentence[INDEX]][0] >= args.tag_dict_min[0]:
                if overt_cat[0] not in tag_dict[sentence[INDEX]]:
                    include_supertag = False
            if include_supertag:
                word_tagged[INDEX] = True
                new_supertags.append(MGcat)
        #now we renormalize, as some supertags have been removed (because of both k and the tag_dict)
        totals = {}
        for st in new_supertags:
            INDEX = st[2]
            if INDEX not in totals:
                totals[INDEX] = st[1]
            else:
                totals[INDEX] += st[1]
        for st in new_supertags:
            INDEX = st[2]
            del(st[2])
            new_prob = (1/totals[INDEX])*st[1]
            st[1] = new_prob
        supertags = new_supertags
        skip_parse = False
        for index in word_tagged:
            if not word_tagged[index]:
                derivation_bracketings = []
                skip_parse = True
                break
        if not skip_parse:
            try:
                with timeout(args.timeout[0]):
                    start_time = default_timer()
                    (parse_time, derivation_bracketings, derived_bracketings, xbar_bracketings, xbar_trees, subcat_derivation_bracketings, subcat_full_derivation_bracketings, full_derivation_bracketings, lex_scores) = main(sentence=(' ').join(sentence), return_bracketings=True, return_xbar_trees=True, allowMoreGoals=True, show_trees=False, print_expressions=False, supertags=supertags, start_time=start_time)
                    end_time = default_timer() - start_time
            except Exception as e:
                sys.stderr.write("\nError!!")
                derivation_bracketings = []
        else:
            sys.stderr.write("\nNo tags were assigned to word at index position "+str(index)+" owing to the tag dict threshold!\n")
        if len(derivation_bracketings) == 0:
            parses[str(line_index)] = "No Parses Found"
            continue
        for i in range(len(xbar_bracketings)):
            sdb = fix_coord_annotation(subcat_derivation_bracketings[0])
            sfdb = fix_coord_annotation(subcat_full_derivation_bracketings[0])
        while "  " in sfdb:
            sfdb = re.sub("  ", " ", sfdb, count=10000)
        parses[str(line_index)] = [derived_bracketings, xbar_bracketings, sfdb, sdb]
    sys.stderr.write("\nFinished parsing sentences.\n")
    with open(args.output_file[0], 'w') as output_file:
        json.dump(parses, output_file)

if __name__ == '__main__':
    cmd_parser = argparse.ArgumentParser(description='Astar Parser command line arguments.')
    cmd_parser.add_argument('input_file', metavar='INPUT_FILE', type=str, nargs=1, help='Specifies the file containing the sentences to be parsed.')
    cmd_parser.add_argument('model_dir', metavar='MODEL_DIR', type=str, nargs=1, help='Specifies the supertagger model folder.')
    cmd_parser.add_argument('output_file', metavar='OUTPUT_FILE', type=str, nargs=1, help='Specifies the name of the file to write the parses to (if a file with this name already exists, it will be overwritten).')
    cmd_parser.add_argument('supertag_type', metavar='SUPERTAG_TYPE', type=str, nargs=1, help="Specifies which type of supertags to use ('abstract' or 'reified'), which is need to find the right mappings file.")
    cmd_parser.add_argument('-k', '-K', dest='k', metavar='K', type=int, nargs=1, default=[40], help='Integer specifying the number of supertags that should be output by the supertagger per word (defaults to 40).')
    cmd_parser.add_argument('--tag-dict-min', dest='tag_dict_min', metavar='M', type=int, nargs=1, default=[3], help='Any word appearing M or more times will only be paired with supertags whose overt anchor was seen with this word during training (defaults to 3).')
    cmd_parser.add_argument('--seed_tag-dict-min', dest='seed_tag_dict_min', metavar='SM', type=int, nargs=1, default=[3], help='Any word appearing M or more times in the seed set will only be paired with supertags whose overt anchor was seen with this word in the seed set during training (defaults to 3).')
    cmd_parser.add_argument('--timeout', dest='timeout', metavar='T', type=int, nargs=1, default=[60], help='Integer specifying a timeout for the parser in seconds (defaults to 60).')
    args = cmd_parser.parse_args()
    if args.supertag_type[0] not in ['abstract', 'reified']:
        raise Exception("Error! supertag type must be either 'abstract' or 'reified'")
    astar_parse(args)
  
