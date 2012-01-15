#include "statmaster.hh"


StatMaster::StatMaster()
{
  d_fp = fopen("stats", "w");
  // setvbuf(d_fp, 0, _IOLBF, 1024);
}

StatMaster::~StatMaster()
{
  fclose(d_fp);
}
void StatMaster::remNameserver(const ComboAddress& remoteIP, const std::string& qname, uint8_t rcode, unsigned int d_usec)
{
  fprintf(d_fp, "%u %u %s %s\n", d_usec, rcode, remoteIP.toStringWithPort().c_str(), qname.c_str());
}
