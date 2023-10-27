#include <string>
#include <unordered_map>
#include <vector>

#include <fstream>
#include <iostream>


// Stores all the unique items
class Items
{
public:
	// get index of an item
	// this represents the position of the binary bit
	// first item is at the LSB and the last item is at the MSB
	inline size_t GetIndex(const std::string& item) { return m_Items[item]; }

	// get the item at an index
	std::string GetItem(size_t index) const
	{
		if (index < m_InsertIndex) // safety check
			for (const auto& item : m_Items)
				if (item.second == index) // index found
					return item.first;
		
		std::cerr << "ERROR: item not found at index " << index << std::endl;
		return "\0";
	}

	// insert an item and stores the index
	void AddItem(const std::string& item)
	{
		if (m_Items.count(item) == 0) // check if item isn't already added
		{
			m_Items[item] = m_InsertIndex;
			m_InsertIndex++;
		}
	}

	// get the total count of items
	inline size_t GetCount() const { return m_InsertIndex; }

	// get a list of all the items
	std::vector<std::string> GetAll() const
	{
		std::vector<std::string> items;
		items.reserve(m_InsertIndex);

		for (auto const& pair : m_Items)
			items.emplace_back(pair.first);

		return items;
	}

private:
	std::unordered_map<std::string, size_t> m_Items;
	size_t m_InsertIndex = 0;
};

// Abstraction over the binary encoding
class Itemset
{
public:
	// Updates the final value after adding the item to it's binary position
	void AddItem(size_t position)
	{
		size_t blockNo = position / 8;

		if (blockNo >= m_Blocks.size()) // handling more than 8 items per transaction
			for (size_t i = 0 ; i <= blockNo ; i++)
				m_Blocks.push_back(0);

		size_t shift = position % 8;
		m_Blocks[blockNo] |= (1 << shift);
	}

	// appends a block to m_Blocks
	inline void AddBlock(const uint8_t block)
	{
		m_Blocks.push_back(block);
	}

	// adds all the items of an itemset to this->itemset
	void AddItemset(const Itemset& itemset)
	{
		const std::vector<uint8_t> blocks = itemset.GetBlocks();

		// append empty blocks to match the size
		while (blocks.size() > m_Blocks.size())
			AddBlock((uint8_t)0);

		// OR the blocks
		for (size_t i = 0; i < blocks.size(); i++)
			m_Blocks[i] |= blocks[i];
	}

	// checks if an itemset has an item
	bool HasItem(size_t position) const
	{
		size_t blockNo = position / 8;
		size_t shift = position % 8;

		return (m_Blocks[blockNo]) & (1 << shift);
	}

	// checks if an itemset is equal to another Itemset
	inline bool IsEqual(const Itemset& itemset) const { return itemset.GetEncodedVal() == GetEncodedVal(); }

	// merges the binary of all the blocks and gives one final encoded value
	size_t GetEncodedVal() const
	{
		size_t encodedVal = 0;
		for (size_t i = 0 ; i < m_Blocks.size() ; ++i)
		{
			size_t temp = 0;
			temp |= m_Blocks[i];
			encodedVal |= temp << (i * 8);
		}
		return encodedVal;
	}

	inline const std::vector<uint8_t> GetBlocks() const { return m_Blocks; }

private:
	std::vector<uint8_t> m_Blocks;
};

static Items ITEMS;
static std::vector<Itemset> TRANSACTIONS;

// parses the transaction file and generates Items and vector<Itemset>
void ReadTransactions(const char* itemsfilePath = "./data/transactions.txt")
{
	std::ifstream itemsFile(itemsfilePath);
	if (itemsFile.is_open())
	{
		std::string line;
		while (std::getline(itemsFile, line))
		{
			Itemset itemset;

			std::string item = "";
			for (char& ch : line)
			{
				if (ch == ',')
				{
					ITEMS.AddItem(item);
					itemset.AddItem(ITEMS.GetIndex(item));

					item = "";
					continue;
				}
				item += ch;
			}

			ITEMS.AddItem(item);
			itemset.AddItem(ITEMS.GetIndex(item));

			TRANSACTIONS.push_back(itemset);
		}
		itemsFile.close();
	}
	else
	{
		std::cerr << "ERROR: unable to open file [" << itemsfilePath << "]" << std::endl;
	}
}

// antecedent : consequent
class Rule
{
public:
	std::vector<std::string> antecedent, consequent;

public:
	Itemset GetAntecedent() const
	{
		Itemset items;

		for (const auto& item : antecedent)
			items.AddItem(ITEMS.GetIndex(item));

		return items;
	}

	Itemset GetConsequent() const
	{
		Itemset items;

		for (const auto& item : consequent)
			items.AddItem(ITEMS.GetIndex(item));

		return items;
	}

	// returns an item set with all the antecedents and consequents added to one itemset
	Itemset ToItemset() const
	{
		Itemset items;

		for (const auto& item : antecedent)
			items.AddItem(ITEMS.GetIndex(item));

		for (const auto& item : consequent)
			items.AddItem(ITEMS.GetIndex(item));

		return items;
	}

	// returns the rule to a printable string
	std::string ToString() const
	{
		std::string rule = "";

		for (const auto& item : antecedent)
		{
			rule += item;
			rule += " ";
		}

		rule += "-> ";

		for (const auto& item : consequent)
		{
			rule += item;
			rule += " ";
		}

		return rule;
	}
};

// the master class that performs the computation
class Apriori
{
public:
	Apriori(float minSupport, float minConfidence, float minLift = -1.0f)
		: m_MinSupport(minSupport), m_MinConfidence(minConfidence), m_MinLift(minLift)
	{
		std::vector<Itemset> c0;
		c0.reserve(ITEMS.GetCount());
		std::vector<Itemset> l0;
		l0.reserve(ITEMS.GetCount());

		// calculate the initial candidate item sets
		for (const auto& item : ITEMS.GetAll())
		{
			Itemset itemset;
			itemset.AddItem(ITEMS.GetIndex(item));
			c0.push_back(itemset);
		}
		
		FrequentItemsets(c0, l0);

		std::vector<Itemset> frequentItemsets;

		size_t i = 0;
		while (i < _MAX_ITR)
		{
			++i;

			CandidateItemsets(c0, l0);
			FrequentItemsets(c0, l0);
			
			if (l0.size() == 0) break;
			frequentItemsets = l0;
		}

		if (i == _MAX_ITR) // reached maximum iterations
			std::cout << "WARNING: Maximum iterations reached." << std::endl;


		for (const auto& frequentSet : frequentItemsets)
		{
			std::cout << "\n{ ";
			std::vector<std::string> frequentItems;
			for (const auto& item : ITEMS.GetAll())
			{
				if (frequentSet.HasItem(ITEMS.GetIndex(item)))
				{
					frequentItems.push_back(item);
					std::cout << item << ", ";
				}
			}
			std::cout << "}" << std::endl;

			GenerateRules(frequentItems);
		}
	}

private:
	// obtain the candidate itemsets
	void CandidateItemsets(std::vector<Itemset>& candidateSets, const std::vector<Itemset>& frequentSets) const
	{
		candidateSets.clear();
		for (size_t i = 0 ; i < frequentSets.size() ; i++)
		{
			size_t valI = frequentSets[i].GetEncodedVal();

			/*
			size_t firstItem = 0;
			while (!frequentSets[i].HasItem(firstItem))
				firstItem++;
			std::cout << "First Item = " << firstItem << std::endl;
			*/

			for (size_t j = i ; j < frequentSets.size() ; j++)
			{
				size_t valJ = frequentSets[j].GetEncodedVal();

				if (valI == valJ) continue; // skip if joining with same set

				// std::cout << valI << " JOIN " << valJ << std::endl;

				Itemset& set = candidateSets.emplace_back();

				set.AddItemset(frequentSets[i]);
				set.AddItemset(frequentSets[j]);
			}
		}
	}

	// obtain the frequent itemsets
	void FrequentItemsets(const std::vector<Itemset>& candidateSets, std::vector<Itemset>& frequentSets) const
	{
		frequentSets.clear();
		for (const auto& set : candidateSets)
			if (Support(set) >= m_MinSupport)
				frequentSets.push_back(set);
	}

	// recursively calculate all possible subsets of a given set
	void CalculateSubsets(std::vector<std::string>& A, std::vector<std::vector<std::string>>& result, std::vector<std::string>& subset, int index) const
	{
		// Add the current subset to the result list
		result.push_back(subset);

		// Generate subsets by recursively including and
		// excluding elements
		for (int i = index; i < A.size(); i++)
		{
			// Include the current element in the subset
			subset.push_back(A[i]);

			// Recursively generate subsets with the current
			// element included
			CalculateSubsets(A, result, subset, i + 1);

			// Exclude the current element from the subset
			// (backtracking)
			subset.pop_back();
		}
	}

	// calculates the subsets of an itemset
	std::vector<std::vector<std::string>> Subsets(std::vector<std::string>& A) const
	{
		std::vector<std::string> subset;
		std::vector<std::vector<std::string>> result;
		int index = 0;
		CalculateSubsets(A, result, subset, index);
		return result;
	}

	// generates the association rules from an itemset
	void GenerateRules(std::vector<std::string>& itemset) const
	{
		std::cout << "Association Rules:" << std::endl;
		std::vector<std::vector<std::string>> subsets = Subsets(itemset);
		for (const auto& subset : subsets)
		{
			if (subset.size() == 1) continue;
			
			// an antecedentPtr is a pointer after which all the items are consequent
			// this is looped to generate all possible rules
			size_t antecedentPtr = 1;
			while (antecedentPtr < subset.size())
			{
				Rule rule;
				
				size_t j = 0;
				for (; j < antecedentPtr; ++j) rule.antecedent.push_back(subset[j]);
				for (; j < subset.size(); ++j) rule.consequent.push_back(subset[j]);
				
				if (Confidence(rule) > m_MinConfidence)
					std::cout << rule.ToString() << std::endl;
				
				antecedentPtr++;
			}
		}
	}

private: // calculate the interestingness measures

	float Support(const Itemset& itemset) const
	{
		int frequency = 0;

		for (const auto& transaction : TRANSACTIONS)
		{
			if ((itemset.GetEncodedVal() & transaction.GetEncodedVal()) == itemset.GetEncodedVal())
				frequency++;
		}

		return (float)frequency / (float)TRANSACTIONS.size();
	}

	float Confidence(const Rule& rule) const
	{
		return Support(rule.ToItemset()) / Support(rule.GetAntecedent());
	}

	float Lift(const Rule& rule) const
	{
		return Confidence(rule) / Support(rule.GetConsequent());
	}

private:
	float m_MinSupport, m_MinConfidence, m_MinLift;
	const size_t _MAX_ITR = 10;
};


int main()
{
	ReadTransactions();
	Apriori algorithm(0.5, 0.7);
}
