#include "dnsparser.hh"
#include "sstuff.hh"
#include "misc.hh"
#include "dnswriter.hh"
#include "dnsrecords.hh"
#include "statbag.hh"
#include "base32.hh"
#include "dnssecinfra.hh"
#include <boost/foreach.hpp>

StatBag S;

// 4033 5
// FIXME: namespace this
enum vState { Indeterminate, Bogus, Insecure, Secure };
const char *vStates[]={"Indeterminate", "Bogus", "Insecure", "Secure"};

// NSEC(3) results
// FIXME: namespace this
enum dState { NODATA, NXDOMAIN, ENT, INSECURE };
const char *dStates[]={"nodata", "nxdomain", "empty non-terminal", "insecure (no-DS proof)"};


typedef std::multimap<uint16_t, DNSKEYRecordContent> keymap_t;


string nsec3Hash(const string &qname, const string &salt, unsigned int iters)
{
  return toBase32Hex(hashQNameWithSalt(iters, salt, qname));
}


// void proveOrDeny(const nsec3set &nsec3s, const string &qname, const string &salt, unsigned int iters, set<string> &proven, set<string> &denied)
// {
//   string hashed = nsec3Hash(qname, salt, iters);

//   // cerr<<"proveOrDeny(.., '"<<qname<<"', ..)"<<endl;
//   // cerr<<"hashed: "<<hashed<<endl;
//   for(nsec3set::const_iterator pos=nsec3s.begin(); pos != nsec3s.end(); ++pos) {
//     string base=(*pos).first;
//     string next=(*pos).second;

//     if(hashed == base)
//     {
//       proven.insert(qname);
//       cout<<qname<<" ("<<hashed<<") proven by base of "<<base<<".."<<next<<endl;
//     }
//     if(hashed == next)
//     {
//       proven.insert(qname);
//       cout<<qname<<" ("<<hashed<<") proven by next of "<<base<<".."<<next<<endl;
//     }
//     if((hashed > base && hashed < next) ||
//        (next < base && (hashed < next || hashed > base)))
//     {
//       denied.insert(qname);
//       cout<<qname<<" ("<<hashed<<") denied by "<<base<<".."<<next<<endl;
//     }
//     if (base == next && base != hashed)
//     {
//       denied.insert(qname);
//       cout<<qname<<" ("<<hashed<<") denied by "<<base<<".."<<next<<endl;
//     }
//   }
// }

class TCPResolver : public boost::noncopyable
{
public:
  TCPResolver(ComboAddress addr)
  {
    d_rsock=new Socket(InterNetwork, Stream);
    d_rsock->connect(addr);
  }

  ~TCPResolver()
  {
    delete d_rsock;
  }

  string query(string qname, uint16_t qtype)
  {
    cerr<<"Q "<<qname<<"/"<<DNSRecordContent::NumberToType(qtype)<<endl;
    vector<uint8_t> packet;
    DNSPacketWriter pw(packet, qname, qtype);

    // recurse
    pw.getHeader()->rd=true;

    // we'll do the validation
    pw.getHeader()->cd=true;
    pw.getHeader()->ad=true;

    // we do require DNSSEC records to do that!
    pw.addOpt(2800, 0, EDNSOpts::DNSSECOK);
    pw.commit();

    uint16_t len;
    len = htons(packet.size());
    if(d_rsock->write((char *) &len, 2) != 2)
      throw PDNSException("tcp write failed");

    d_rsock->writen(string((char*)&*packet.begin(), (char*)&*packet.end()));
    
    if(d_rsock->read((char *) &len, 2) != 2)
      throw PDNSException("tcp read failed");

    len=ntohs(len);
    char *creply = new char[len];
    int n=0;
    int numread;
    while(n<len) {
      numread=d_rsock->read(creply+n, len-n);
      if(numread<0)
        throw PDNSException("tcp read failed");
      n+=numread;
    }

    string reply(creply, len);
    delete[] creply;

    return reply;
  }

  Socket *d_rsock;
};

// lifted from syncres with some changes
struct RRIDComp
{
  bool operator()(const pair<string, QType>& a, const pair<string, QType>& b) const
  {
    if(pdns_ilexicographical_compare(a.first, b.first))
      return true;
    if(pdns_ilexicographical_compare(b.first, a.first))
      return false;

    return a.second < b.second;
  }
};

typedef map<pair<string, QType>, set<shared_ptr<DNSRecordContent> >, RRIDComp > rrsetmap_t;

typedef pair<string, uint16_t> NT; // Name/Type pair
typedef std::multimap<NT, shared_ptr<DNSRecordContent> > recmap_t;
typedef std::multimap<NT, RRSIGRecordContent> sigmap_t;
typedef std::multimap<NT, shared_ptr<DNSRecordContent> > nsecmap_t;

bool compareDS(DSRecordContent a, DSRecordContent b)
{
  return a.d_tag == b.d_tag &&
         a.d_algorithm == b.d_algorithm &&
         a.d_digesttype == b.d_digesttype &&
         a.d_digest == b.d_digest;
}

typedef pair<string, uint16_t> ZT; //Zonename/keyTag pair
// recmap_t g_recs; // fetched recs for full chain validation
// keymap_t g_keys; // fetched keys
// keymap_t g_vkeys; // validated keys

// FIXME: needs a zone argument, to avoid things like 6840 4.1
dState getDenial(rrsetmap_t &validrrsets, string qname, uint16_t qtype)
{
  std::multimap<string, NSEC3RecordContent> nsec3s;

  for(rrsetmap_t::const_iterator i=validrrsets.begin(); i!=validrrsets.end(); ++i)
  {
    // FIXME also support NSEC
    if(i->first.second != QType::NSEC3) continue;
    
    for(set<shared_ptr<DNSRecordContent> >::const_iterator j=i->second.begin(); j!=i->second.end(); ++j) {
      NSEC3RecordContent ns3r = dynamic_cast<NSEC3RecordContent&> (**j);
      // nsec3.insert(new nsec3()
      // cerr<<toBase32Hex(r.d_nexthash)<<endl;
      nsec3s.insert(make_pair(i->first.first, ns3r));
    }
  }
  cerr<<"got "<<nsec3s.size()<<" NSEC3s"<<endl;
  for(std::multimap<string,NSEC3RecordContent>::const_iterator i=nsec3s.begin(); i != nsec3s.end(); ++i) {
      vector<string> parts;
      // FIXME: should strip zone name instead of just finding first dot
      boost::split(parts, i->first, boost::is_any_of("."));
      string base=toLower(parts[0]);
      string next=toLower(toBase32Hex(i->second.d_nexthash));
      string salt = i->second.d_salt;
      uint16_t iters = i->second.d_iterations;
      string hashed = nsec3Hash(qname, salt, iters);
      cerr<<base<<" .. ? "<<hashed<<" ? .. "<<next<<endl;
      if(base==hashed) {
        // positive name proof, need to check type
        cerr<<"positive name proof, checking type bitmap"<<endl;
        cerr<<"d_set.count("<<qtype<<": "<<i->second.d_set.count(qtype)<<endl;
      } else if ((hashed > base && hashed < next) ||
                (next < base && (hashed < next || hashed > base))) {
        bool optout=(1 & i->second.d_flags);
        cerr<<"negative name proof, optout = "<<optout<<endl;
        if(qtype == QType::DS && optout) return INSECURE;
      }
  }
}

void validateWithKeySet(rrsetmap_t& rrsets, rrsetmap_t& rrsigs, rrsetmap_t& validated, keymap_t& keys)
{
  for(rrsetmap_t::const_iterator i=rrsets.begin(); i!=rrsets.end(); i++)
  {
    cerr<<"validating "<<(i->first.first)<<"/"<<i->first.second.getName()<<endl;
    pair<rrsetmap_t::const_iterator, rrsetmap_t::const_iterator> r = rrsigs.equal_range(make_pair(i->first.first, i->first.second));
    for(rrsetmap_t::const_iterator j=r.first; j!=r.second; j++) {
      for(set<shared_ptr<DNSRecordContent> >::const_iterator k=j->second.begin(); k!=j->second.end(); k++) {
        vector<shared_ptr<DNSRecordContent> > toSign;
        set<shared_ptr<DNSRecordContent> > rrs = rrsets[make_pair(stripDot(j->first.first), j->first.second)];
        toSign.assign(rrs.begin(), rrs.end());

        const RRSIGRecordContent rrc=dynamic_cast<const RRSIGRecordContent&> (*(*k));

        if(!keys.count(rrc.d_tag)) continue;

        string msg=getMessageForRRSET(j->first.first, rrc, toSign);
        pair<keymap_t::const_iterator, keymap_t::const_iterator> r = keys.equal_range(rrc.d_tag);
        for(keymap_t::const_iterator l=r.first; l!=r.second; l++) {
          if(DNSCryptoKeyEngine::makeFromPublicKeyString(l->second.d_algorithm, l->second.d_key)->verify(msg, rrc.d_signature)) {
            validated[make_pair(stripDot(j->first.first), j->first.second)] = rrs;
            cerr<<"valid"<<endl;
            // FIXME: break out enough levels
          }
        }
      }
    }
  }
}

// returns vState
// should return vState, zone cut and validated keyset
// i.e. www.7bits.nl -> insecure/7bits.nl/[]
//      www.powerdnssec.org -> secure/powerdnssec.org/[keys]
//      www.dnssec-failed.org -> bogus/dnssec-failed.org/[]

vState getKeysFor(TCPResolver& tr, string zone)
{
  vector<string> labels;
  vState state;

  state = Indeterminate;

  stringtok(labels, zone, ".");

  string qname="";
  typedef std::multimap<uint16_t, DSRecordContent> dsmap_t;
  dsmap_t dsmap;
  keymap_t keymap;
  recmap_t recs;

  state = Secure;
  while(qname.size() < zone.size())
  {
    if(qname == "")
    {
      DSRecordContent rootanchor=dynamic_cast<DSRecordContent&> (*(DNSRecordContent::mastermake(QType::DS, 1, "19036 8 2 49aac11d7b6f6446702e54a1607371607a1a41855200fd2ce1cdde32f24e8fb5")));
      dsmap.clear();
      dsmap.insert(make_pair(19036, rootanchor));
    }
  
    recs.clear();
    vector<RRSIGRecordContent> sigs;
    vector<shared_ptr<DNSRecordContent> > toSign;

    keymap_t tkeymap; // tentative keys
    keymap.clear();
    
    // start of this iteration
    // we can trust that dsmap has valid DS records for qname

    cerr<<"got DS for ["<<qname<<"], grabbing DNSKEYs"<<endl;
    MOADNSParser mdp(tr.query(qname, QType::DNSKEY));

    for(MOADNSParser::answers_t::const_iterator i=mdp.d_answers.begin(); i!=mdp.d_answers.end(); ++i) {
      if(stripDot(i->first.d_label) != qname)
        continue;

      if(i->first.d_type == QType::RRSIG)
      {
        RRSIGRecordContent rrc=dynamic_cast<RRSIGRecordContent&> (*(i->first.d_content));
        if(rrc.d_type != QType::DNSKEY)
          continue;
        sigs.push_back(rrc);
      }
      else if(i->first.d_type == QType::DNSKEY)
      {
        DNSKEYRecordContent drc=dynamic_cast<DNSKEYRecordContent&> (*(i->first.d_content));
        tkeymap.insert(make_pair(drc.getTag(), drc));
        toSign.push_back(i->first.d_content);
      }
    }
    cerr<<"got "<<keymap.size()<<" keys and "<<sigs.size()<<" sigs"<<endl;

    for(dsmap_t::const_iterator i=dsmap.begin(); i!=dsmap.end(); i++)
    {
      DSRecordContent dsrc=i->second;
      cerr<<"got DS with tag "<<dsrc.d_tag<<", got "<<tkeymap.count(i->first)<<" DNSKEYs for tag"<<endl;
      pair<keymap_t::const_iterator, keymap_t::const_iterator> r = tkeymap.equal_range(i->first);
      for(keymap_t::const_iterator j=r.first; j!=r.second; j++)
      {
        DNSKEYRecordContent drc=j->second;
        DSRecordContent dsrc2=makeDSFromDNSKey(qname, drc, dsrc.d_digesttype);
        if(compareDS(dsrc, dsrc2))
        {
          cerr<<"got valid DNSKEY"<<endl;
          keymap.insert(make_pair(drc.getTag(), drc));
        }
      }
    }

    cerr<<"got "<<keymap.size()<<"/"<<tkeymap.size()<<" valid/tentative keys"<<endl;
    // these counts could be off if we somehow ended up with 
    // duplicate keys. Should switch to a type that prevents that.
    if(keymap.size() < tkeymap.size())
    {
      // this should mean that we have one or more DS-validated DNSKEYs
      // but not a fully validated DNSKEY set, yet
      // one of these valid DNSKEYs should be able to validate the
      // whole set
      for(vector<RRSIGRecordContent>::const_iterator i=sigs.begin(); i!=sigs.end(); i++)
      {
        cerr<<"got sig for keytag "<<i->d_tag<<" matching "<<tkeymap.count(i->d_tag)<<" keys of which "<<keymap.count(i->d_tag)<<" valid"<<endl;
        string msg=getMessageForRRSET(qname, *i, toSign);
        pair<keymap_t::const_iterator, keymap_t::const_iterator> r = keymap.equal_range(i->d_tag);
        for(keymap_t::const_iterator j=r.first; j!=r.second; j++) {
          cerr<<"validating"<<endl;
          cerr<<DNSCryptoKeyEngine::makeFromPublicKeyString(j->second.d_algorithm, j->second.d_key)->verify(msg, i->d_signature)<<endl;
          if(DNSCryptoKeyEngine::makeFromPublicKeyString(j->second.d_algorithm, j->second.d_key)->verify(msg, i->d_signature))
          {
            cerr<<"validation succeeded - whole DNSKEY set is valid"<<endl;
            keymap=tkeymap;
            break;
          }
        }
        if(!keymap.size()) cerr<<"did not manage to validate DNSKEY set based on DS-validated KSK, only passing KSK on"<<endl;
      }
    }

    if(!keymap.size())
    {
      cerr<<"ended up with zero valid DNSKEYs, going Bogus"<<endl;
      state=Bogus;
      break;
    }
    cerr<<"situation: we have one or more valid DNSKEYs for ["<<qname<<"]; walking downwards to find DS"<<endl;
    do {
      qname=stripDot(labels.back()+"."+qname);
      labels.pop_back();
      cerr<<"next name ["<<qname<<"], trying to get DS"<<endl;

      recs.clear();
      sigs.clear();
      dsmap_t tdsmap; // tentative DSes
      dsmap.clear();
      toSign.clear();

      MOADNSParser mdp(tr.query(qname, QType::DS));

      rrsetmap_t rrsets;
      rrsetmap_t rrsigs;

      for(MOADNSParser::answers_t::const_iterator i=mdp.d_answers.begin(); i!=mdp.d_answers.end(); ++i) {
        cerr<<"res "<<i->first.d_label<<"/"<<i->first.d_type<<endl;
        if(i->first.d_type == QType::OPT) continue;

        if(i->first.d_type == QType::RRSIG) {
          RRSIGRecordContent rrc = dynamic_cast<RRSIGRecordContent&> (*(i->first.d_content));
          rrsigs[make_pair(stripDot(i->first.d_label),rrc.d_type)].insert(i->first.d_content);
        }
        else {
          rrsets[make_pair(stripDot(i->first.d_label),i->first.d_type)].insert(i->first.d_content);
        }
      }

      rrsetmap_t validrrsets;
      validateWithKeySet(rrsets, rrsigs, validrrsets, keymap);

      cerr<<"got "<<rrsets.count(make_pair(qname,QType::DS))<<" DS of which "<<validrrsets.count(make_pair(qname,QType::DS))<<" valid "<<endl;

      pair<rrsetmap_t::const_iterator, rrsetmap_t::const_iterator> r = validrrsets.equal_range(make_pair(qname, QType::DS));
      for(rrsetmap_t::const_iterator i=r.first; i!=r.second; i++) {
        for(set<shared_ptr<DNSRecordContent> >::const_iterator j=i->second.begin(); j!=i->second.end(); j++)
        {
          const DSRecordContent dsrc=dynamic_cast<const DSRecordContent&> (**j);
          dsmap.insert(make_pair(dsrc.d_tag, dsrc));
        }
      }
      if(!dsmap.size()) {
        cerr<<"no DS at this level, checking for denials"<<endl;
        dState dres = getDenial(validrrsets, qname, QType::DS);
        if(dres == INSECURE) return Insecure;
      }
    } while(!dsmap.size() && labels.size());

    if(!labels.size()) {
      cerr<<"ran out of labels, aborting"<<endl;
      exit(0);
    }
    // break;
  }

  return state;
}

void get(recmap_t &res, TCPResolver &tr, string qname, uint16_t qtype, int depth=0)
{
  recmap_t recs; // all records that we fetched
  sigmap_t sigs;
  nsecmap_t nsecs;

  cerr<<"at depth "<<depth<<" fetching "<<qname<<"/"<<DNSRecordContent::NumberToType(qtype)<<endl;
  if(res.count(NT(qname, qtype)))
  {
    cerr<<"already got those, returning"<<endl;
    return;
  }
  if(qname=="" and qtype==QType::DS) {
    res.insert(make_pair(NT("", QType::DS), DNSRecordContent::mastermake(QType::DS, 1, "19036 8 2 49aac11d7b6f6446702e54a1607371607a1a41855200fd2ce1cdde32f24e8fb5")));
    cerr<<"DS/. - returning root anchor"<<endl;
    return;
  }

  MOADNSParser mdp(tr.query(qname, qtype));

  set<string> signers;
  for(MOADNSParser::answers_t::const_iterator i=mdp.d_answers.begin(); i!=mdp.d_answers.end(); ++i) {
    cerr<<"ZR ("<<i->first.d_place<<") "<<i->first.d_label<<" "<<DNSRecordContent::NumberToType(i->first.d_type)<<" "<<i->first.d_content->getZoneRepresentation()<<endl;    
    if(i->first.d_type == QType::RRSIG)
    {
      RRSIGRecordContent rrc=dynamic_cast<RRSIGRecordContent&> (*(i->first.d_content));
      signers.insert(stripDot(rrc.d_signer));
    }

    if(i->first.d_type == QType::RRSIG || i->first.d_place == DNSRecord::Answer) {
      res.insert(make_pair(NT(stripDot(i->first.d_label), i->first.d_type), i->first.d_content));
    }
  }

  if(qtype == QType::DNSKEY)
  {
    cerr<<"got DNSKEYs, grabbing DSes"<<endl;
    get(res, tr, qname, QType::DS, depth+1);
    return;
  }

  if(signers.size())
  {
    cerr<<"got RRSIGs, getting DNSKEYs"<<endl;
    for(set<string>::const_iterator i=signers.begin(); i!=signers.end(); ++i)
    {
      get(res, tr, *i, QType::DNSKEY, depth+1);
    }
    return;
  }
}

int main(int argc, char** argv)
try
{
  reportAllTypes();

  if(argc < 5) {
    cerr<<"Syntax: oneshot IP-address port question question-type\n";
    exit(EXIT_FAILURE);
  }

  string qname=argv[3];

  ComboAddress dest(argv[1] + (*argv[1]=='@'), atoi(argv[2]));
  TCPResolver tr(dest);



  cout<<"end state "<<vStates[getKeysFor(tr, qname)]<<endl;
  // cout<<"got "<<recs.size()<<" unverified records"<<endl;

  // pair<recmap_t::const_iterator,recmap_t::const_iterator> r = make_pair(recs.begin(), recs.end());
  // for(recmap_t::const_iterator i=r.first; i!=r.second; i++)
  // {
  //   cout<<i->first.first<<" "<<DNSRecordContent::NumberToType(i->first.second)<<" "<<i->second->getZoneRepresentation()<<endl;
  // }

  // cout<<"verify result: "<<verify(recs, qname, qtype)<<endl;
  // // fetch requested result
  // MOADNSParser mdpA(tr.query(qname, qtype));

  // vector<shared_ptr<DNSRecordContent> > ARecords;
  // RRSIGRecordContent rrc;


  // vector<shared_ptr<DNSRecordContent> > DNSKEYRecords;
  // for(MOADNSParser::answers_t::const_iterator i=mdpDNSKEY.d_answers.begin(); i!=mdpDNSKEY.d_answers.end(); ++i) {
  //   if(i->first.d_type == QType::DNSKEY && i->first.d_place == DNSRecord::Answer) {
  //     DNSKEYRecords.push_back(i->first.d_content);
  //   }
  // }
  // cerr<<"got "<<DNSKEYRecords.size()<<" DNSKEY records"<<endl;

  // string msg=getMessageForRRSET(qname, rrc, ARecords);
  // BOOST_FOREACH(shared_ptr<DNSRecordContent> r, DNSKEYRecords) {
  //   DNSKEYRecordContent drc = dynamic_cast<DNSKEYRecordContent&>(*(r));
  //   if(rrc.d_tag==drc.getTag())
  //     cerr<<"Verify with DNSKEY "<<drc.getTag()<<": "<<DNSCryptoKeyEngine::makeFromPublicKeyString(drc.d_algorithm, drc.d_key)->verify(msg, rrc.d_signature)<<endl;
  // }

  exit(EXIT_SUCCESS);
}
catch(std::exception &e)
{
  cerr<<"Fatal: "<<e.what()<<endl;
}
