
from neo4j import GraphDatabase
import os
from neo4j import Transaction
import pandas as pd

BASE_PATH = "C:/Users/Andrea/Documents/ETH/FS25/MasterThesis/silicon/graphExports/"
# BASE_PATH = "C:/Users/Andrea/Documents/ETH/FS25/MasterThesis/gobra/graphExports/"
URI = "neo4j+ssc://df418be1.databases.neo4j.io"
AUTH = ("neo4j", os.environ['NEO4J-PW'])


ASSUMPTION_NODE_TYPES = """["Inhale", "Assumption", "Infeasible", "Label"]"""
ASSERTION_NODE_TYPES = """["Exhale", "Assertion", "Check"]"""

driver = GraphDatabase.driver(URI, auth=AUTH)
session = driver.session(database="neo4j")
driver.verify_connectivity()

def create_id_uniquness_constraint(tx: Transaction, node_label: str):
    tx.run(f"""CREATE CONSTRAINT `id_{node_label}_uniq` IF NOT EXISTS
    FOR (n: {node_label})
    REQUIRE (n.`id`) IS UNIQUE;""")
    tx.run(f"""CREATE INDEX {node_label}_pos_index IF NOT EXISTS 
           FOR (n:{node_label}) ON (n.position)""")
    tx.run(f"""CREATE INDEX {node_label}_assumption_type_index IF NOT EXISTS 
           FOR (n:{node_label}) ON (n.`assumption type`)""")
    tx.run(f"""CREATE INDEX {node_label}_node_type_index IF NOT EXISTS 
           FOR (n:{node_label}) ON (n.`node type`)""")

def create_indices(tx: Transaction, label: str, node_label_postfix: str):
    tx.run(f"""CREATE INDEX {label}{node_label_postfix}_pos_index IF NOT EXISTS 
           FOR (n:{label}{node_label_postfix}) ON (n.position)""")


def load_nodes(tx: Transaction, file_path: str, node_label: str):
    with open(file_path, "r") as f:
        nodes_raw = pd.read_csv(f, sep="#")
    nodes = []
    for _, e in nodes_raw.iterrows():
        nodes.append(dict(e))
    tx.run(f"""
        UNWIND $nodes AS row
        WITH row
        WHERE NOT toInteger(row.`id`) IS NULL
        CALL {{
            WITH row
            MERGE (n: {node_label} {{ `id`: toInteger(row.`id`) }})
            SET n.`id` = toInteger(row.`id`)
            SET n.`node type` = row.`node type`
            SET n.`assumption type` = row.`assumption type`
            SET n.`node info` = row.`node info`
            SET n.`source info` = row.`source info`
            SET n.`position` = row.`position`
            SET n.`fine grained source` = row.`fine grained source`
        }};
        """
        , nodes=nodes
    )

def load_edges(tx: Transaction, file_path: str, node_label: str):
    with open(file_path, "r") as f:
        edges_raw = pd.read_csv(f, sep=",")
    edges = []
    for _, e in edges_raw.iterrows():
        edges.append(dict(e))
    # print(edges)
    tx.run(f"""
        UNWIND $edges AS row
        WITH row 
        CALL {{
        WITH row
            MATCH (source: {node_label} {{ `id`: toInteger(row.`source`) }})
            MATCH (target: {node_label} {{ `id`: toInteger(row.`target`) }})
            MERGE (source)-[r: `flows_into`]->(target)
            SET r.`type` = row.`label`
        }};
        """
        , edges=edges
    )

def import_graph2(tx: Transaction, foldername: str, node_label: str, is_overwrite=True):
    if is_overwrite:
        delete_nodes_detach(tx, node_label, "")
    load_nodes(tx, foldername + "/nodes.csv", node_label)
    load_edges(tx, foldername + "/edges.csv", node_label)

def import_low_level_graph(foldername: str, node_label: str):
    session.execute_write(create_id_uniquness_constraint, node_label) # transaction!
    session.execute_write(import_graph2, foldername, node_label) # transaction!

def delete_nodes_detach(tx, label, node_label_postfix):
    print(f"delete nodes {label}{node_label_postfix}")
    tx.run(f"MATCH (n:{label}{node_label_postfix}) DETACH DELETE n;")

def create_nodes(tx, label, node_label_postfix, assumption_node_selection):
    print(f"create nodes {label}{node_label_postfix}")
    tx.run(f"""
    MATCH (a:{label})
    WHERE {assumption_node_selection.replace("$ID", "a")} 
    MERGE (aNew :{label}{node_label_postfix} {{`source info`: a.`source info`, position: a.position}})
    RETURN aNew;
           """) # OR a.`node type` IN {ASSERTION_NODE_TYPES}
    
def create_infeasibility_nodes(tx, label, node_label_postfix):
    print(f"create infeasibility nodes")
    tx.run(f"""
    MATCH (c:{label})-[r:flows_into]->(a:{label}), 
          (c1:{label}{node_label_postfix})
    WHERE a.`node type` = "Infeasible"
    AND  c1.`source info` = c.`source info` AND c1.position = c.position
    MERGE (c1)-[:flows_into]->(aNew :{label}{node_label_postfix} {{`source info`: a.`source info`, position: a.position, `node type`: a.`node type`}})
    RETURN aNew;
           """)
    tx.run(f"""
    MATCH (c:{label})-[r1:flows_into]->(b:{label})-[r2:flows_into]->(a:{label}), (a1:{label}{node_label_postfix}), (c1:{label}{node_label_postfix})
    WHERE a.`node type` = "Infeasible"
    AND  c1.`source info` = c.`source info` AND c1.position = c.position
    AND  a1.`source info` = a.`source info` AND a1.position = a.position AND a1.`node type` = a.`node type`
    MERGE (c1)-[:flows_into]->(a1)
    RETURN a1;
           """)
    tx.run(f"""
    MATCH (a:{label})-[r1:flows_into]->(c:{label}), (a1:{label}{node_label_postfix}), (c1:{label}{node_label_postfix})
    WHERE a.`node type` = "Infeasible"
    AND  c1.`source info` = c.`source info` AND c1.position = c.position
    AND  a1.`source info` = a.`source info` AND a1.position = a.position AND a1.`node type` = a.`node type`
    MERGE (a1)-[:flows_into]->(c1)
    RETURN a1;
           """)

def create_direct_edges(tx, label, node_label_postfix, assumption_node_selection):
    print(f"add direct edges")
    tx.run(f"""
    MATCH (a:{label})-[r2:flows_into]->(c:{label}),
    (a1:{label}{node_label_postfix}), (c1:{label}{node_label_postfix})
    WHERE {assumption_node_selection.replace("$ID", "a")} AND a1.`source info` = a.`source info` AND a1.position = a.position
    AND a.`node type` IN {ASSUMPTION_NODE_TYPES}
    AND  c1.`source info` = c.`source info` AND c1.position = c.position
    AND c.`node type` IN {ASSERTION_NODE_TYPES}
    AND a1 <> c1
    MERGE (a1)-[n:flows_into]->(c1)
    RETURN a1;
    """)

def create_indirect_edges(tx, label, node_label_postfix, assumption_node_selection):
    print(f"add indirect edges")
    tx.run(f"""
    MATCH (a:{label})-[r:flows_into]->(b:{label})
    ((b1:{label})-[:flows_into]->(b2:{label})){{0, 5}}
    (b3:{label})-[r2:flows_into]->(c:{label}),
    (a1:{label}{node_label_postfix}), (c1:{label}{node_label_postfix})
    WHERE all(x in (b + b1 + b2) where NOT (x.`node type` IN {ASSUMPTION_NODE_TYPES} AND {assumption_node_selection.replace("$ID", "x")}))
    AND all(x in (b + b1 + b2) where (NOT x.`node type` = "Infeasible"))
    AND  {assumption_node_selection.replace("$ID", "a")} AND a.`node type` IN {ASSUMPTION_NODE_TYPES}
    AND  c.`node type` IN {ASSERTION_NODE_TYPES}
    AND a1.`source info` = a.`source info` AND a1.position = a.position
    AND c1.`source info` = c.`source info` AND c1.position = c.position
    AND a1 <> c1
    MERGE (a1)-[n:flows_into]->(c1)
    RETURN a1;
           """)
    
    # print("add edges across method calls")
    # # add edges for joined graphs
    # tx.run(f"""
    # MATCH (a:{label})-[r:flows_into]->(c:{label}),
    # (a1:{label}{node_label_postfix}), (c1:{label}{node_label_postfix})
    # WHERE a.`node type` IN {ASSERTION_NODE_TYPES}
    # AND  c.`node type` IN {ASSUMPTION_NODE_TYPES} AND NOT c.`assumption type` IN {internal_assumption_types}
    # AND a1.`source info` = a.`source info` AND a1.position = a.position
    # AND c1.`source info` = c.`source info` AND c1.position = c.position
    # AND a1 <> c1
    # MERGE (a1)-[n:flows_into]->(c1)
    # RETURN a1, n, c1;
    #        """)

def import_graph_view(label, is_overwrite, node_label_postfix, assumption_node_selection):
    if is_overwrite:
        session.execute_write(delete_nodes_detach, label, node_label_postfix)
    session.execute_write(create_indices, label, node_label_postfix)
    session.execute_write(create_nodes, label, node_label_postfix, assumption_node_selection)
    session.execute_write(create_infeasibility_nodes, label, node_label_postfix)
    session.execute_write(create_direct_edges, label, node_label_postfix, assumption_node_selection)
    session.execute_write(create_indirect_edges, label, node_label_postfix, assumption_node_selection)

def import_graph_without_internal_nodes(label, is_overwrite=True):
    node_label_postfix = "_NonInternal"
    internal_assumption_types = """["Internal", "Trigger"]"""
    assumption_node_selection = f"NOT $ID.`assumption type` IN {internal_assumption_types}"
    import_graph_view(label, is_overwrite, node_label_postfix, assumption_node_selection)
    print("non internal view done")

def import_graph_with_explicit_nodes_only(label, is_overwrite=True):
    node_label_postfix = "_Explicit"
    explicit_assumption_types = """["Explicit", "ExplicitPostcondition"]"""
    assumption_node_selection = f"$ID.`assumption type` IN {explicit_assumption_types}"
    import_graph_view(label, is_overwrite, node_label_postfix, assumption_node_selection)
    print("explicit view done")
    
foldername = input("foldername: ")
node_label = input("node label: ")
import_low_level_graph(foldername, node_label)
print("Low-level graph imported successfully")
# import_graph_with_explicit_nodes_only(node_label)
# print("Explicit-only Viper graph imported successfully")
import_graph_without_internal_nodes(node_label)
print("Viper graph imported successfully")
session.close()
driver.close()