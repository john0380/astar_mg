#!/usr/bin/env python
from nltk import tokenize
import re
import string
import copy
from timeout import timeout
import cky_mg
import astar_mg
import argparse
import sys
import pdb
import json
import os
from timeit import default_timer

cat_pattern = re.compile('\w+')
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
cat_pattern = re.compile('\w+')
brackets='()'
open_b, close_b = brackets
open_pattern, close_pattern = (re.escape(open_b), re.escape(close_b))
node_pattern = '[^%s%s]+' % (open_pattern, close_pattern)
leaf_pattern = '[^%s%s]+' % (open_pattern, close_pattern)
sel_variables = ['x', 'y', 'z', 'w']

def main(sent,k,best_k,file_line_num,data_dir,model_dir,time_out_secs=600,tag_dict_threshold=3,seed_tag_dict_threshold=3,max_move_dist=None,null_c_lexicon=None):
    sent = re.sub("&", "ANDANDAND", sent, count=100)
    end_time=None
    words = tokenize.word_tokenize(sent)
    index=-1
    for word in words:
        index+=1
        if words[index] == "ANDANDAND":
            words[index] = "&"
    words_to_remove = []
    for i in range(len(words)):
        if words[i] in punctuation or words[i] == "''":
            words_to_remove.append(words[i])
    while len(words_to_remove) > 0:
        words.remove(words_to_remove[0])
        del(words_to_remove[0])
    for i in range(len(words)):
        words[i] = words[i].lower()
        try:
            float(words[i])
            words[i] = 'num'
        except ValueError:
            x=0
    if len(words) == 0:
        sys.stderr.write("no sentence found at line "+file_line_num)
        return (None,None,None,None,None,None)
    if tag_dict_threshold != None:
        tag_dict = json.load(open(data_dir+'/tag_dict'))
    if seed_tag_dict_threshold != None:
        seed_tag_dict = json.load(open(data_dir+'/seed_tag_dict'))
    REF_MGST_table = json.load(open(data_dir+'/REF_MGST_table'))
    supertag_lists = []
    for INDEX in range(len(words)):
        supertag_list = [st for st in best_k[INDEX].split('\t')[2:] if st[0] != '<']
        if supertag_list[-1][-1] == '\n':
            supertag_list[-1] = supertag_list[-1][:-1]
        supertag_lists.append(supertag_list)
    supertags = []
    for INDEX in range(len(words)):
        for supertag in supertag_lists[INDEX]:
            parts = supertag.split(' ')
            supertags.append([REF_MGST_table[parts[0]], float(parts[1]), INDEX])
    new_supertags = []
    word_tagged = {}
    for supertag in supertags:
        supertag = copy.deepcopy(supertag)
        INDEX = supertag[2]
        if INDEX not in word_tagged:
            word_tagged[INDEX] = False
        st = supertag[0]
        if type(st[0][0][0]) != type([]) and type(st[0][0][0]) != type(()):
            if st[0][0] == 'OVERT_WORD':
                overt_cat = copy.deepcopy(st)
                st[0] = (words[INDEX], st[0][1], st[0][2])
            st[2] = INDEX
        else:
            for link in st:
                if link[0][0][0] == 'OVERT_WORD':
                    overt_cat = copy.deepcopy(link[0])
                    link[0][0] = (words[INDEX], link[0][0][1], link[0][0][2])
                if link[0][2] == None:
                    link[0][2] = INDEX
                if link[2][0][0] == 'OVERT_WORD':
                    overt_cat = copy.deepcopy(link[2])
                    link[2][0] = (words[INDEX], link[2][0][1], link[2][0][2])
                if link[2][2] == None:
                    link[2][2] = INDEX
        include_supertag = True
        seed_threshold_met = False
        if seed_tag_dict_threshold != None:
            if words[INDEX] in seed_tag_dict and seed_tag_dict[words[INDEX]][0] >= seed_tag_dict_threshold:
                seed_threshold_met = True
                if overt_cat[0] not in seed_tag_dict[words[INDEX]]:
                    include_supertag = False
        if tag_dict_threshold != None and not seed_threshold_met:
            if words[INDEX] in tag_dict and tag_dict[words[INDEX]][0] >= tag_dict_threshold:
                if overt_cat[0] not in tag_dict[words[INDEX]]:
                    include_supertag = False
        if include_supertag:
            word_tagged[INDEX] = True
            new_supertags.append(supertag)
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
            with timeout(time_out_secs):
                start_time = default_timer()
                (parse_time, derivation_bracketings, derived_bracketings, xbar_bracketings, xbar_trees, subcat_derivation_bracketings, subcat_full_derivation_bracketings, full_derivation_bracketings, lex_scores) = astar_mg.main(sentence=(' ').join(words), show_trees=False, print_expressions=False, return_bracketings=True, return_xbar_trees=True, allowMoreGoals=True, printPartialAnalyses=False, limitRightwardMove=False, supertags=supertags, start_time=start_time, MAXMOVEDIST=None, null_c_lexicon=null_c_lexicon)
                end_time = default_timer() - start_time
        except NameError:
            sys.stderr.write("Parser Error!")
            derivation_bracketings = []
    else:
        sys.stderr.write("\nNo tags were assigned to word at index position "+str(index)+" owing to the tag dict threshold!\n")
    if len(derivation_bracketings) == 0:
        sys.stderr.write("\nNo parses discovered!\n")
        return (None,None,None,None,None,None)
    else:
        if len(derivation_bracketings) > 1:
            text = " parses discovered.\n"
        else:
            text = " parse discovered.\n"
        sys.stderr.write("\n"+str(len(derivation_bracketings))+text)
    got_PTB_DEPS = False
    xbar_trees = []
    derivation_trees = []
    subcat_derivation_trees = []
    subcat_full_derivation_trees = []
    full_derivation_trees = []
    derived_trees = []
    return (derivation_bracketings[0], derived_bracketings[0], xbar_bracketings[0], subcat_derivation_bracketings[0], subcat_full_derivation_bracketings[0], full_derivation_bracketings[0],end_time)

def get_null_c_lexicon(null_lexicon, null_c_lexicon, abstract_tags):
    #we no longer just take c heads out of the supertags, but also the null heads with the
    #the licensee features for A'-movement..
    for entry in null_lexicon:
        if entry[0] in ['[det]', '[dat]', '[topicalizer]', '[focalizer]', '[wh]', '[relativizer]']:
            #because relative clauses have a nominal layer which is selected for by a determiner,
            #that determiner has no c= feature so we will not detect it.. we therefore have no choice but to allow
            #null [det] into the null_c_lexicon and also [dat] which governs [det] in coordinate constructions
            null_c_lexicon.append(entry)
            continue
        for feature in entry[1]:
            if '\xe2\x89\x88' not in feature.encode('utf8'):
                #we don't include stuff that adjoins to CP in the null_c_lexicon, only
                #stuff that selects it as complement (or spec)
                if cat_pattern.search(feature).group(0).lower() == 'c':
                    if abstract_tags:
                        entry = strip_features(entry)
                        if entry not in null_c_lexicon:
                            null_c_lexicon.append(entry)
                    else:
                        null_c_lexicon.append(entry)
                    break

def strip_features(cat):
    if type(cat) == type(u"") or type(cat) == type(""):
        parts = cat.split(" ")
        features = parts[1].split(" ")
    else:
        features = cat[1]
        new_cat = copy.deepcopy(cat)
    i = -1
    for feature in features:
        i+=1
        subcat_features = re.search('{.*?}', feature)
        if subcat_features:
            subcat_features = subcat_features.group(0)
        else:
            subcat_features = []
        sfs = []
        for sf in subcat_features:
            if sf in ['EDGE', '+NONE', 'MAIN', 'ANA', 'IT']+sel_variables:
                sfs.append(sf)
        if len(sfs) == 0:
            sfs = ''
        else:
            sfs = "{"+".".join(sfs)+"}"
        feature = re.sub('{.*}', sfs, feature)
        if type(cat) != type(u"") and type(cat) != type(""):
            new_cat[1][i] = feature
        else:
            features[i] = feature
    if type(cat) == type(u"") or type(cat) == type(""):
        new_cat = unicode(parts[0]+" "+" ".join(features))
    return new_cat

if __name__ == '__main__':
    cmd_parser = argparse.ArgumentParser(description='command line arguments.')
    cmd_parser.add_argument('--input_file', dest='input_file', metavar='input_file', type=str, nargs=1, help='The input file containing the test sentences.')
    cmd_parser.add_argument('--best_k', dest='best_k', metavar='k', type=int, default=[40], nargs=1, help='The max number of supertags the supertagger should provide for each word (defaults to 40).')
    cmd_parser.add_argument('--data_dir', dest='data_dir', metavar='data_dir', type=str, nargs=1, help='The directory containing the test data.')
    cmd_parser.add_argument('--model_dir', dest='model_dir', metavar='model_dir', type=str, nargs=1, help='The directory containing the model.')
    cmd_parser.add_argument('--time_out', dest='time_out', metavar='time_out', type=int, default=[600], nargs=1, help='The timeout in seconds for the parser (defaults to 600 seconds).')
    cmd_parser.add_argument('--tag_dict_threshold', dest='tag_dict_threshold', metavar='tag_dict_threshold', type=int, default=[3], nargs=1, help='The tag dictionary threshold (defaults to 3).')
    cmd_parser.add_argument('--seed_tag_dict_threshold', dest='seed_tag_dict_threshold', metavar='seed_tag_dict_threshold', type=int, default=[3], nargs=1, help='The tag dictionary threshold for the hand-crafted corpus (defaults to 3).')
    cmd_parser.add_argument('--max_move_dist', dest='max_move_dist', metavar='max_move_dist', type=int, default=[50], nargs=1, help='The maximum number of words in the string a constituent can move across (defaults to 50).')
    cmd_parser.add_argument('--no_abar', dest='no_abar', metavar='no_abar', type=str, nargs=1, default=['False'], help="Set to True if the supertags do not include A'-movement triggering null heads.")
    cmd_parser.add_argument('--abstract_tags', dest='abstract_tags', type=str, default=['False'], metavar='abstract_tags', nargs=1, help='Set to True if using abstract supertags.')
    cmd_parser.add_argument('--stop_after', dest='stop_after', metavar='stop_after', type=int, default=[100000], nargs=1, help='The number of parses to generate before stopping (defaults to 100,000).')
    cmd_parser.add_argument('--start_line', dest='start_line', metavar='start_line', type=int, nargs=1, help='Specifies which line to begin parsing at.')
    cmd_parser.add_argument('--end_line', dest='end_line', metavar='end_line', type=int, nargs=1, help='Specifies the last line of the file to parse.')
    cmd_parser.add_argument('--file_suffix', dest='file_suffix', metavar='file_suffix', type=str, nargs=1, help='The suffix to be appended to the file name of the json.')
    cmd_parser.add_argument('--add_to_existing', dest='add_to_existing', type=str, default=['False'], metavar='add_to_existing', nargs=1, help='Set to True if you want to keep the existing parses.')
    args = cmd_parser.parse_args()
    if args.add_to_existing[0] == "True":
        add_to_existing = True
    else:
        add_to_existing = False
    stop_after = int(args.stop_after[0])
    start_line = int(args.start_line[0])
    end_line = int(args.end_line[0])
    time_out = int(args.time_out[0])
    sys.stderr.write("\nParsing sentences "+str(args.start_line[0])+" to "+str(args.end_line[0])+" with timeout of "+str(time_out)+" seconds and tag_dict_threshold "+str(args.tag_dict_threshold[0])+" and seed_tag_dict_threshold "+str(args.seed_tag_dict_threshold[0])+"...\n")
    if args.no_abar[0].lower() not in ['true', 'false', '1', '0']:
        raise Exception("--no-abar must take True or False as argument")
    else:
        if args.no_abar[0].lower() in ['true', '1']:
            no_abar = True
        else:
            no_abar = False
    if args.abstract_tags[0].lower() not in ['true', 'false', '1', '0']:
        raise Exception("--abstract-tags must take True or False as argument")
    else:
        if args.abstract_tags[0].lower() in ['true', '1']:
            abstract_tags = True
        else:
            abstract_tags = False
    if no_abar:
        CovertLexicon = json.load(open("wsj_MGbankSeed/CovertLexicon"))
        ExtraposerLexicon = json.load(open("wsj_MGbankSeed/ExtraposerLexicon"))
        TypeRaiserLexicon = json.load(open("wsj_MGbankSeed/TypeRaiserLexicon"))
        ToughOperatorLexicon = json.load(open("wsj_MGbankSeed/ToughOperatorLexicon"))
        NullExcorporatorLexicon = json.load(open("wsj_MGbankSeed/NullExcorporatorLexicon"))
        null_c_lexicon = []
        for lexicon in [CovertLexicon, ExtraposerLexicon, TypeRaiserLexicon, ToughOperatorLexicon, NullExcorporatorLexicon]:
            get_null_c_lexicon(lexicon, null_c_lexicon, abstract_tags)
    else:
        CovertLexicon = None
        ExtraposerLexicon = None
        TypeRaiserLexicon = None
        ToughOperatorLexicon = None
        NullExcorporatorLexicon = None
        null_c_lexicon = []
    if "parses"+args.file_suffix[0]+'_'+str(start_line)+'_'+str(end_line) in os.listdir(args.model_dir[0]):
        tags_parses = json.load(open(args.model_dir[0]+"/"+"parses"+args.file_suffix[0]+'_'+str(start_line)+'_'+str(end_line)))
    else:
        tags_parses = []
    parse_nums = []
    master_parses_lookup = {}
    try:
        master_parses = json.load(open(args.model_dir[0]+"/"+"master_parses"))
    except Exception as e:
        master_parses = []
    for entry in master_parses:
        if entry['trees'] != [None,None,None,None,None,None]:
            master_parses_lookup[entry['parse_num']] = entry
    sentences = open(args.input_file[0],'r')
    best_k_results = open(args.model_dir[0]+'/best_'+str(args.best_k[0]),'r')
    best_ks = [[]]
    for bk in best_k_results:
        if bk == '\n':
            best_ks.append([])
            continue
        best_ks[-1].append(bk)
    best_ks_index = -1
    sent_index = -1
    num_sents_processed = 0
    num_sents_parsed = 0
    for sentence in sentences:
        sent_index+=1
        if sent_index < start_line or str(sent_index) in master_parses_lookup:
            continue
        elif sent_index > end_line:
            break
        num_sents_processed+=1
        if sentence[-1] == '\n':
            sentence = sentence[:-1]
        try:
            (derivation_bracketing, derived_bracketing, xbar_bracketing, subcat_derivation_bracketing, subcat_full_derivation_bracketing, full_derivation_bracketing,end_time) = main(sentence,args.best_k[0],best_ks[sent_index],sent_index,args.data_dir[0],args.model_dir[0],time_out,args.tag_dict_threshold[0],args.seed_tag_dict_threshold[0],args.max_move_dist[0],null_c_lexicon)
            tags_parses.append({'sentence':sentence,'parse_num':str(sent_index),'best_k':best_ks[sent_index],'trees':[subcat_derivation_bracketing, xbar_bracketing, derived_bracketing, subcat_full_derivation_bracketing, derivation_bracketing, full_derivation_bracketing],'end_time':end_time})
        except Exception as e:
            try:
                sys.stderr.write("\n"+e[0])
            except Exception as e:
                pass
            xbar_bracketing = None
        if xbar_bracketing != None:
            num_sents_parsed+=1
            if num_sents_parsed == stop_after:
                break
        sys.stderr.write("\nNumber of sentences successfully parsed: "+str(num_sents_parsed)+"/"+str(num_sents_processed)+"\n")
        with open(args.model_dir[0]+"/"+"parses"+args.file_suffix[0]+'_'+str(start_line)+'_'+str(end_line), "w") as parse_results:
            json.dump(tags_parses, parse_results)
    sys.stderr.write("\nSaved parses in: "+args.model_dir[0]+"/"+"parses"+args.file_suffix[0]+'_'+str(start_line)+'_'+str(end_line)+'\n')








    
